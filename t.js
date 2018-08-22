const fs = require('fs')
const path = require('path')
const crypto = require('crypto')
const _ = require('lodash')
const parser = require('@babel/parser')
const traverse = require('@babel/traverse').default
const generate = require('@babel/generator').default
const sha1 = str => crypto.createHash('sha1').update(str).digest('hex')
const log = 0 ? console.log : () => {}

const DEBUG = true

const root_path = '/home/wangjie/Workspace/tb/core/lib'
// const root_path = '/home/wangjie/Workspace/tmp/js'

const ls_files = dir_path => {
  const files = []
  return new Promise((resolve, reject) => {
    fs.readdir(dir_path, async (err, sub_files) => {
      if (err) reject(err)

      for (const filename of sub_files) {
        const file = path.join(dir_path, filename)
        const stat = fs.statSync(file)
        if (stat.isFile() && filename.endsWith('.js')) files.push(file)
        if (stat.isDirectory()) {
          const sub_files = await ls_files(file)
          sub_files.forEach(f => files.push(f))
        }
      }

      resolve(files)
    })
  })
}

const parse_file = file_path => {
  return new Promise((resolve, reject) => {
    fs.readFile(file_path, (err, data) => {
      if (err) reject(err)
      const code = data.toString()
      const hash = sha1(code)
      const module_path = get_module_path(file_path)
      const ast = parser.parse(code)
      const name = path.parse(file_path).name
      resolve({ast, file_path, hash, name, module_path})
    })
  }).catch(err => {
    throw new Error(`parse error in ${file_path}`)
  })
}

const create_dir = file_path => {
  if (fs.existsSync(path)) return
  const dir = path.parse(file_path).dir
  if (!fs.existsSync(dir)) create_dir(dir)
  else fs.mkdirSync(file_path)
}

const write_file = (file_path, data, cb) => {
  const dir = path.parse(file_path).dir
  if (!fs.existsSync(dir)) create_dir(dir)
  fs.writeFile(file_path, data, cb)
}

const get_module_path = file_path => {
  const s = file_path.indexOf('lib')
  const e = file_path.indexOf('.js')
  return file_path.slice(s + 4, e)
}

const get_cache_path = file_path => {
  const module_path = get_module_path(file_path)
  const cache_dir = path.join(__dirname, 'caches')
  const cache_path = path.join(cache_dir, module_path + '.json')
  return cache_path
}

const load_and_parse_file = file_path => {
  const module_path = get_module_path(file_path)
  const cache_path = get_cache_path(file_path)
  return new Promise(async (resolve, reject) => {
    if (fs.existsSync(cache_path) && fs.statSync(cache_path).isFile()) {
      log('loading cache:', module_path)
      fs.readFile(cache_path, (err, data) => {
        if (err) reject(err)
        let mod
        try {
          mod = JSON.parse(data.toString())
        } catch (e) {
          log('load bad cache:', module_path)
          fs.unlinkSync(cache_path)
          mod = load_and_parse_file(file_path)
        }
        log('cache loaded:', module_path)
        resolve(mod)
      })
    } else {
      log('parsing:', module_path)
      const mod = await parse_file(file_path)
      write_file(cache_path, JSON.stringify(mod, null, 2), err => {
        if (err) reject(err)
        resolve(mod)
      })
    }
  })
}

const travel_ast = ast => {
  const imported = {}
  const exported = {}
  const called = {}
  const assignment = {}
  const classes = {}
  const callable = {}

  const handle_property = property => {
    if (property.type === 'MemberExpression') {
      return '[' + handle_object(property) + ']'
    } else return property.name
  }

  const handle_object = node => {
    if (node.type === 'CallExpression') {
      return handle_object(node.callee) + '()'
    } else if (node.type === 'MemberExpression') {
      return handle_object(node.object) + '.' + handle_property(node.property)
    } else return node.name
  }

  const handle_function_stack = (path, stack = []) => {
    if (path.node.type === 'FunctionExpression'
    || path.node.type === 'FunctionDeclaration'
    || path.node.type === 'ClassMethod') {

      if (path.node.id) stack.unshift(path.node.id)
      else {
        const code = get_node_code(path.node)
        const hash = sha1(code)
        const re = Object.values(callable).find(i => i.hash === hash)
        const step = {
          name: re ? re.name : 'Anonymous',
          line: path.node.loc.start.line,
          hash,
        }
        stack.push(step)
      }
    }
    if (path.parentPath) {
      handle_function_stack(path.parentPath, stack)
    }
    return stack
  }

  const handle_classes = path => {
    if (path.node.type === 'ClassDeclaration') {
      const c = {}
      if (path.node.superClass) {
        c.extends = path.node.superClass.name
      }
      const class_name = path.node.id.name
      c.methods = path.node.body.body.map(node => {
        if (node.type === 'ClassMethod') {
          const code = get_node_code(node)
          return {
            name: node.key.name,
            code,
            hash: sha1(code),
          }
        }
      }).filter(i => i)
      classes[class_name] = c
      c.methods.forEach(method => {
        callable[class_name + '.' + method.name] = {
          code: method.code,
          hash: method.hash,
          name: class_name + '.' + method.name,
          type: 'ClassMethod',
        }
      })
    }
  }

  const get_node_code = node => generate(node, {minified: true, comments: false}).code

  const handle_import = path => {
    if (path.node.type === 'VariableDeclarator'
      && path.node.init
      && path.node.init.type === 'CallExpression'
      && path.node.init.callee.name === 'require') {
      const mod_name = path.node.init.arguments[0].value
      if (path.node.id.type === 'ObjectPattern') {
        path.node.id.properties.forEach(node => {
          const key = node.key.name
          const value = node.value.name
          imported[value] = mod_name + '.' + key
        })
      } else {
        const name = path.node.id.name
        imported[name] = mod_name
      }
    }
  }
  const handle_call = path => {
    if (path.node.type === 'CallExpression') {
      const call_method = handle_object(path.node.callee)
      called[call_method] = handle_function_stack(path)
    }
  }

  const handle_assignment = path => {
    let left
    let right
    if (path.node.type === 'AssignmentExpression') {
      left = handle_object(path.node.left)
      const right_code = get_node_code(path.node.right)
      right = {
        hash: sha1(right_code),
        type: path.node.right.type,
        code: right_code,
      }
      if (left === 'module.exports') {
        exported['export'] = right
      }
    }
    if (path.node.type === 'VariableDeclarator') {
      left = path.node.id.name
      if (path.node.init) {
        const right_code = get_node_code(path.node.init)
        right = {
          hash: sha1(right_code),
          type: path.node.init.type,
          code: right_code,
        }
      } else {
        right = {
          hash: sha1('undefined'),
          type: 'Identifier',
          code: 'undefined',
        }
      }
    }
    if (left && right) {
      assignment[left] = right
      if (['FunctionExpression', 'FunctionDeclaration'].includes(right.type)) {
        callable[left] = Object.assign({}, right, {name: left})
      }
    }
  }

  traverse(ast, {
    enter(path) {
      handle_assignment(path)
      handle_classes(path)
      handle_import(path)
      handle_call(path)
    }
  })

  return {
    imported,
    called,
    assignment,
    classes,
    exported,
    callable,
  }
}

// ^^^^ pre-process part

const handle_and_write_mod = mod => {
  if (!FP && mod.result) return
  console.log('handling mod:', mod.module_path)
  mod.result = travel_ast(mod.ast)
  const cache_path = get_cache_path(mod.file_path)
  return new Promise((resolve, reject) => {
    write_file(cache_path, JSON.stringify(mod, null, 2), err => {
      if (err) reject(err)
      resolve(mod)
    })
  })
}

const flat_obj = obj => {
  const re = []
  for (let k in obj) {
    if (_.isEmpty(obj[k])) re.push(k)
    else re.push(flat_obj(obj[k]))
  }
  return re
}

/**
 *
 * @param {String} entity_name
 * @param {Object<String, Module>} mods
 */
const search_entity_in_mods = (entity_name, mods) => {

  // return class
  const find_class = class_name => {
    for (let mod_name in mods) {
      if (mods[mod_name].classes && mods[mod_name].classes[class_name]) {
        return mods[mod_name].classes[class_name]
      }
    }
  }

  const extend_class_method = child_mod_name => {
    for (let class_name in mods[child_mod_name].classes) {
      const parent_class_name = mods[child_mod_name].classes[class_name].extends
      if (!parent_class_name) continue
      const parent_class = find_class(parent_class_name)
      if (!parent_class) continue
      parent_class.methods.forEach(method => {
        mods[child_mod_name].callable[class_name + '.' + method.name] = {
          code: method.code,
          hash: method.hash,
          name: class_name + '.' + method.name,
          type: 'ClassMethod',
        }
      })
      // mods[child_mod_name].classes[class_name].methods = _.concat(mods[child_mod_name].classes[class_name].methods, parent_class.methods)
    }
  }

  for (let mod_name in mods) extend_class_method(mod_name)

  // 判断一个模块是否引入了另一个模块，如果引入了返回变量名
  const mod_imported = (parent_mod_name, child_mod_name) => {
    if (parent_mod_name.startsWith('lib/')) parent_mod_name = parent_mod_name.substr(4)
    if (child_mod_name.startsWith('lib/')) child_mod_name = child_mod_name.substr(4)
    for (const [var_name, mod_name] of _.entries(mods[child_mod_name].imported)) {
      let true_mod_name = mod_name.split('.').shift()
      if (true_mod_name.startsWith('lib/')) true_mod_name = true_mod_name.substr(4)
      if (!(true_mod_name in mods)) true_mod_name += '/index'
      if (true_mod_name === parent_mod_name) return var_name
    }
  }

  // judge if a method be used in a module 返回调用该方法的方法名
  const call_in_mod = (parent_mod_name, method_name, child_mod_name) => {
    if (parent_mod_name && parent_mod_name.startsWith('lib/')) parent_mod_name = parent_mod_name.substr(4)
    if (child_mod_name.startsWith('lib/')) child_mod_name = child_mod_name.substr(4)
    // 如果一个模块引入了另一个模块，并且执行了一个前一个模块定义的方法，则（大致可以）认为该模块调用了前一个模块定义的方法
    let var_name
    if (parent_mod_name) {
      var_name = mod_imported(parent_mod_name, child_mod_name)
      if (!var_name) return false
    }
    const FUZZY_MATCH_METHOD = true
    const called_methods = {}
    for (const [called_method_name, stack] of _.entries(mods[child_mod_name].called)) {
      if (//parent_mod_name && ~called_method_name.toLowerCase().indexOf(var_name.toLowerCase()) ||
      ~called_method_name.toLowerCase().indexOf(method_name.toLowerCase())) {
        for (const step of stack) {
          const called_method = mods[child_mod_name].callable.find(i => i.hash === step.hash)
          if (called_method) called_methods[called_method.name] = called_method
        }
        // called_methods[called_method_name] = Object.assign({}, stack, {mod_name: child_mod_name})
      }
    }
    return called_methods
  }

  // find all mods required this mod
  const find_req_mods = (
    to_find_mod_path, // 上一个（子）模块的名字
    methods_name, // 需要包含的方法
    list = [] // 引用栈，避免循环
  ) => {
    const map = {}
    for (let mod_path in mods) {

        if (!_.isEmpty(methods_name)) {
          const new_methods = {}
          for (const method_name of methods_name) {
            const called_methods = call_in_mod(mod_path, method_name, to_find_mod_path)
            if (_.isEmpty(called_methods)) continue
            Object.assign(new_methods, called_methods)
          }
          list = list.slice()
          list.push(mod_path)
          map[mod_path] = find_req_mods(mod_path, Object.keys(new_methods), list)
        } else if (mod_imported(mod_path, to_find_mod_path)) {
          list = list.slice()
          list.push(mod_path)
          map[mod_path] = find_req_mods(mod_path, null, list)
        } else continue

    }
    return map
  }

  const call_in_mods = {}
  for (let mod_path in mods) {
    for (let method_name in mods[mod_path].result.called) {
      const methods = call_in_mod(null, method_name, mod_path)
      call_in_mods[mod_path] = find_req_mods(mod_path, methods)
      // if (method_name.startsWith(entity_name)) {
      //   call_in_mods[mod_path] = find_req_mods(mod_path, method_name)
      // }
    }
  }

  console.log(call_in_mods)
  const flatted_obj = flat_obj(call_in_mods)
  const final_mods = _.uniq(_.flattenDeep(flatted_obj)).filter(i => i.startsWith('api'))
  write_file(path.join(__dirname, 're/apis.txt'), final_mods.join('\n'), err => {
    console.log('done')
  })
  console.log(final_mods)
  return call_in_mods
}

const SF = 0
const FP = 0

const main = async () => {
  const start = Date.now()
  const file_paths = await ls_files(root_path)
  if (SF) {
    const mod = await load_and_parse_file(file_paths[0])
    await handle_and_write_mod(mod)
    console.log(mod.file_path)
    console.log(mod)
  } else {
    const mods = await Promise.all(file_paths.map(load_and_parse_file))
    const load_time = Date.now()
    console.log('mods count:', mods.length, 'time spent:', load_time - start + 'ms')
    await Promise.all(mods.map(handle_and_write_mod))
    const mods_map = _.mapValues(_.keyBy(mods, i => {
      return get_module_path(i.file_path)
    }), mod => _.pick(mod, ['hash', 'name', 'result']))
    const handle_time = Date.now()
    console.log('handled time spent:', handle_time - load_time + 'ms')
    search_entity_in_mods('redis', mods_map) // tbd
  }
}

main()

/**
 *
 * 依赖关系
 *
 * 如果一个模块引入了另一个模块，并且执行了一个前一个模块定义的方法，则（大致可以）认为该模块调用了前一个模块定义的方法
 *
 *
 *
 * 方法 -> 包含了该方法的模块 -> 引入了该模块的模块 -> 递归
 *          ^                   ^
 *        以及使用该方法的位置    调用前一个模块的方法的位置
 *          ^                   ^
 *        模块内的调用栈   ->    模块内的调用栈 -> 合并
 *
 *
 * support:
 *  - commonjs module import / export
 */
