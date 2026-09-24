// =====================================================================
// Expression.js
// 中缀逻辑表达式解析器 + 真值表生成器（纯函数，无 DOM 依赖）
//
// 支持的运算符（优先级从高到低）:
//   NOT(非)  >  AND(与)  >  XOR(异或)  >  OR(或)
//
// 中缀语法（支持括号，大小写不敏感）:
//   与   AND : &   &&   ·   ∧   *   AND   与
//   或   OR  : |   ||   ∨   +   OR   或
//   非   NOT : !   ~    ¬       NOT   非   （前缀）
//   异或 XOR : ^   ⊕           XOR   异或
//   常量      : 0 / 1
//   变量      : 由字母/数字/下划线/中文组成的标识符
//
// 与原有逆波兰管线的衔接：
//   - 中缀表达式经 astToRpn 转为逆波兰字符串后，复用 LogicParser 生成 BDD 图。
//   - XOR 映射为逆波兰 "= <"（即 NOT(XNOR)），无需改动 BDD 构造器。
// =====================================================================

var Expression = (function () {

    var MULTI_OPS = { "&&": "AND", "||": "OR" };
    var SINGLE_OPS = {
        "&": "AND", "·": "AND", "∧": "AND", "*": "AND",
        "|": "OR", "∨": "OR", "+": "OR",
        "!": "NOT", "~": "NOT", "¬": "NOT",
        "^": "XOR", "⊕": "XOR"
    };
    var WORD_OPS = {
        "AND": "AND", "OR": "OR", "NOT": "NOT", "XOR": "XOR",
        "与": "AND", "或": "OR", "非": "NOT", "异或": "XOR"
    };

    function isBlank(ch) { return /\s/.test(ch); }

    function isIdentChar(ch) {
        return /[A-Za-z0-9_一-龥]/.test(ch);
    }

    // ---- 词法分析 ----
    function tokenizeInfix(str) {
        var tokens = [];
        var i = 0, n = str.length;
        while (i < n) {
            var ch = str[i];
            if (isBlank(ch)) { i++; continue; }
            if (ch === '(') { tokens.push({ type: 'lparen', value: ch, pos: i }); i++; continue; }
            if (ch === ')') { tokens.push({ type: 'rparen', value: ch, pos: i }); i++; continue; }

            var two = str.substr(i, 2);
            if (MULTI_OPS[two]) { tokens.push({ type: 'op', value: MULTI_OPS[two], raw: two, pos: i }); i += 2; continue; }
            if (SINGLE_OPS[ch]) { tokens.push({ type: 'op', value: SINGLE_OPS[ch], raw: ch, pos: i }); i++; continue; }

            if (isIdentChar(ch)) {
                var start = i;
                while (i < n && isIdentChar(str[i])) i++;
                var word = str.slice(start, i);
                var upper = word.toUpperCase();
                if (WORD_OPS[upper] !== undefined) {
                    tokens.push({ type: 'op', value: WORD_OPS[upper], raw: word, pos: start });
                } else {
                    tokens.push({ type: 'var', value: word, pos: start });
                }
                continue;
            }

            throw { message: '未知符号 "' + ch + '"', position: i };
        }
        return tokens;
    }

    // ---- 递归下降解析（or -> xor -> and -> not -> primary）----
    function parseInfix(str) {
        var tokens = tokenizeInfix(str);
        if (tokens.length === 0) {
            throw { message: '表达式为空', position: 0 };
        }
        var end = str.length;
        var cursor = { i: 0 };

        function peek() { return tokens[cursor.i]; }

        function error(msg, pos) {
            if (pos === undefined) {
                pos = peek() ? peek().pos : (end > 0 ? end - 1 : 0);
            }
            throw { message: msg, position: pos };
        }

        function parseOr() {
            var left = parseXor();
            while (peek() && peek().type === 'op' && peek().value === 'OR') {
                cursor.i++;
                var right = parseXor();
                left = { type: 'or', left: left, right: right };
            }
            return left;
        }

        function parseXor() {
            var left = parseAnd();
            while (peek() && peek().type === 'op' && peek().value === 'XOR') {
                cursor.i++;
                var right = parseAnd();
                left = { type: 'xor', left: left, right: right };
            }
            return left;
        }

        function parseAnd() {
            var left = parseNot();
            while (peek() && peek().type === 'op' && peek().value === 'AND') {
                cursor.i++;
                var right = parseNot();
                left = { type: 'and', left: left, right: right };
            }
            return left;
        }

        function parseNot() {
            if (peek() && peek().type === 'op' && peek().value === 'NOT') {
                cursor.i++;
                return { type: 'not', operand: parseNot() };
            }
            return parsePrimary();
        }

        function parsePrimary() {
            var tk = peek();
            if (!tk) { error('缺少操作数'); }
            if (tk.type === 'lparen') {
                var openPos = tk.pos;
                cursor.i++;
                var inner = parseOr();
                var close = peek();
                if (!close || close.type !== 'rparen') {
                    error('括号未闭合（缺少右括号）', openPos);
                }
                cursor.i++;
                return inner;
            }
            if (tk.type === 'var') {
                cursor.i++;
                if (tk.value === '0') return { type: 'const', value: 0 };
                if (tk.value === '1') return { type: 'const', value: 1 };
                return { type: 'var', name: tk.value };
            }
            if (tk.type === 'op') {
                error('缺少操作数（运算符 "' + tk.raw + '" 缺少操作数）', tk.pos);
            }
            error('语法错误', tk.pos);
        }

        var ast = parseOr();
        if (peek()) {
            var tk = peek();
            if (tk.type === 'rparen') {
                error('多余的右括号', tk.pos);
            } else if (tk.type === 'op') {
                error('缺少操作数（运算符 "' + tk.raw + '" 后缺少操作数）', tk.pos);
            } else {
                error('无法解析的符号 "' + tk.value + '"', tk.pos);
            }
        }
        return ast;
    }

    // ---- AST -> 逆波兰 token 数组 ----
    function astToRpnTokens(ast) {
        var out = [];
        function walk(node) {
            switch (node.type) {
                case 'var': out.push(node.name); break;
                case 'const': out.push(String(node.value)); break;
                case 'not': walk(node.operand); out.push('<'); break;
                case 'and': walk(node.left); walk(node.right); out.push('.'); break;
                case 'or': walk(node.left); walk(node.right); out.push(','); break;
                case 'xor': walk(node.left); walk(node.right); out.push('='); out.push('<'); break;
            }
        }
        walk(ast);
        return out;
    }

    // ---- 变量收集（按首次出现顺序）----
    function collectVarsFromAst(ast) {
        var seen = {}, vars = [];
        function walk(node) {
            if (!node) return;
            if (node.type === 'var') {
                if (!seen[node.name]) { seen[node.name] = true; vars.push(node.name); }
                return;
            }
            if (node.operand) walk(node.operand);
            if (node.left) walk(node.left);
            if (node.right) walk(node.right);
        }
        walk(ast);
        return vars;
    }

    // ---- 求值 ----
    function evalAst(ast, env) {
        switch (ast.type) {
            case 'var': return env[ast.name] ? 1 : 0;
            case 'const': return ast.value;
            case 'not': return evalAst(ast.operand, env) ? 0 : 1;
            case 'and': return (evalAst(ast.left, env) && evalAst(ast.right, env)) ? 1 : 0;
            case 'or': return (evalAst(ast.left, env) || evalAst(ast.right, env)) ? 1 : 0;
            case 'xor': return (evalAst(ast.left, env) !== evalAst(ast.right, env)) ? 1 : 0;
        }
        return 0;
    }

    // ---- 逆波兰：分词 / 收集变量 / 求值（与 LogicParser 的分词一致）----
    function rpnTokens(str) {
        return str.split(/(\.|,|<|>|=|\s)/).filter(function (t) {
            return t !== '' && !/\s/.test(t);
        });
    }

    function collectVarsFromRpn(tokens) {
        var ops = { '.': 1, ',': 1, '<': 1, '>': 1, '=': 1 };
        var seen = {}, vars = [];
        for (var i = 0; i < tokens.length; i++) {
            var t = tokens[i];
            if (!ops[t] && t !== '0' && t !== '1' && !seen[t]) {
                seen[t] = true;
                vars.push(t);
            }
        }
        return vars;
    }

    function evalRpn(tokens, env) {
        var stack = [];
        for (var i = 0; i < tokens.length; i++) {
            var t = tokens[i], a, b;
            if (t === '.') { b = stack.pop(); a = stack.pop(); stack.push((a && b) ? 1 : 0); }
            else if (t === ',') { b = stack.pop(); a = stack.pop(); stack.push((a || b) ? 1 : 0); }
            else if (t === '<') { a = stack.pop(); stack.push(a ? 0 : 1); }
            else if (t === '>') { b = stack.pop(); a = stack.pop(); stack.push((!a || b) ? 1 : 0); }
            else if (t === '=') { b = stack.pop(); a = stack.pop(); stack.push((a === b) ? 1 : 0); }
            else if (t === '0') { stack.push(0); }
            else if (t === '1') { stack.push(1); }
            else { stack.push(env[t] ? 1 : 0); }
        }
        return stack.length ? (stack[0] ? 1 : 0) : 0;
    }

    // ---- 真值表 ----
    function buildTruthTable(vars, evalFn) {
        var n = vars.length;
        var total = 1 << n;
        var rows = [];
        for (var mask = 0; mask < total; mask++) {
            var env = {}, vals = [];
            for (var i = 0; i < n; i++) {
                var bit = (mask >> (n - 1 - i)) & 1;
                env[vars[i]] = bit;
                vals.push(bit);
            }
            rows.push({ vals: vals, result: evalFn(env) });
        }
        return { vars: vars, rows: rows };
    }

    // ---- 顶层入口 ----
    function analyze(input, mode) {
        var vars, evalFn, rpnString;
        if (mode === 'rpn') {
            var trimmed = (input || '').replace(/^\s+|\s+$/g, '');
            if (trimmed === '') { throw { message: '表达式为空', position: 0 }; }
            var tokens = rpnTokens(trimmed);
            vars = collectVarsFromRpn(tokens);
            evalFn = function (env) { return evalRpn(tokens, env); };
            rpnString = trimmed;
        } else {
            var ast = parseInfix(input || '');
            vars = collectVarsFromAst(ast);
            evalFn = function (env) { return evalAst(ast, env); };
            rpnString = astToRpnTokens(ast).join(' ');
        }
        return {
            mode: mode,
            vars: vars,
            rpnString: rpnString,
            truthTable: buildTruthTable(vars, evalFn)
        };
    }

    return {
        tokenizeInfix: tokenizeInfix,
        parseInfix: parseInfix,
        analyze: analyze,
        rpnTokens: rpnTokens,
        buildTruthTable: buildTruthTable
    };
})();
