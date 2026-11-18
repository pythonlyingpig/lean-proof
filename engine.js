/* Lean 證明機 — 驗證引擎
 * 解析 Lean 4 的一個子集（有限型別上的命題邏輯），窮舉所有可能世界來檢查定理。
 * 等同於 Lean 的 `decide`：有限、可判定的命題，一個一個情況檢查。
 * 瀏覽器（window.LeanEngine）與 Node（module.exports）共用。
 */
(function (root) {
'use strict';

class LeanError extends Error {
  constructor(msg, tok) {
    super(msg);
    this.line = tok && tok.line ? tok.line : null;
  }
}

const KEYWORDS = new Set(['then', 'else', 'with', 'fun', 'match', 'if', 'let', 'at', 'in', 'by', 'do',
  'from', 'deriving', 'where', 'have', 'show', 'forall', 'exists']);
const COMMANDS = new Set(['theorem', 'lemma', 'example', 'def', 'abbrev', 'inductive', 'instance',
  'namespace', 'end', 'open', 'section', 'set_option', 'import', 'variable', 'structure', 'class',
  'attribute', 'deriving', 'noncomputable', 'private', 'protected', 'universe', 'macro', 'syntax',
  'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'mutual', 'opaque', 'axiom']);
const SYMS = ['<->', '<;>', ':=', '=>', '->', '/\\', '\\/', '∃!', '!=', '==', '&&', '||', '^^', '<=', '>=',
  '<|', '|>', '→', '↔', '∧', '∨', '¬', '∀', '∃', '≠', '≤', '≥', '×', 'λ', '↦', '⟨', '⟩', '·',
  '(', ')', '{', '}', '[', ']', ',', ':', '|', ';', '=', '<', '>', '+', '-', '*', '/', '%', '!', '@', '$', '.', '?'];
const SYM_ALIAS = { '->': '→', '<->': '↔', '/\\': '∧', '\\/': '∨', '<=': '≤', '>=': '≥', 'λ': 'fun', '↦': '=>' };

const NODE_LIMIT = 4000000;
const MAX_MODELS = 300;
const MAX_TRACE = 600;

/* ───────────── 斷詞 ───────────── */
function tokenize(src) {
  const toks = [], comments = [];
  const n = src.length;
  let i = 0, line = 1, lineStart = 0, lineHasTok = false, prevEnd = -1;
  const idStart = c => c !== 'λ' && c !== 'Π' && c !== 'Σ' && /[\p{L}_]/u.test(c);
  const idCont = c => /[\p{L}\p{N}_']/u.test(c);
  const push = (t, v, s, e) => {
    toks.push({ t, v, line, col: s - lineStart, s, e, nl: !lineHasTok, adj: s === prevEnd });
    lineHasTok = true; prevEnd = e;
  };
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; lineStart = i; lineHasTok = false; continue; }
    if (c === ' ' || c === '\t' || c === '\r' || c === ' ' || c === '　' || c === '﻿') { i++; continue; }
    if (c === '-' && src[i + 1] === '-') {
      let j = i; while (j < n && src[j] !== '\n') j++;
      comments.push({ line, endLine: line, text: src.slice(i + 2, j).trim(), own: !lineHasTok, block: false });
      i = j; continue;
    }
    if (c === '/' && src[i + 1] === '-') {
      const startLine = line; let depth = 1, j = i + 2;
      while (j < n && depth > 0) {
        if (src[j] === '/' && src[j + 1] === '-') { depth++; j += 2; }
        else if (src[j] === '-' && src[j + 1] === '/') { depth--; j += 2; }
        else { if (src[j] === '\n') { line++; lineStart = j + 1; } j++; }
      }
      let text = src.slice(i + 2, depth === 0 ? j - 2 : j);
      if (text[0] === '-' || text[0] === '!') text = text.slice(1);
      comments.push({ line: startLine, endLine: line, text: text.trim(), own: true, block: true });
      i = j; continue;
    }
    if (idStart(c) || (c === '#' && idStart(src[i + 1] || ''))) {
      let j = i + 1;
      for (;;) {
        while (j < n && idCont(src[j])) j++;
        if (src[j] === '.' && j + 1 < n && (idStart(src[j + 1]) || /[0-9]/.test(src[j + 1]))) { j++; continue; }
        break;
      }
      push('id', src.slice(i, j), i, j); i = j; continue;
    }
    if (/[0-9]/.test(c)) {
      let j = i; while (j < n && /[0-9]/.test(src[j])) j++;
      push('num', src.slice(i, j), i, j); i = j; continue;
    }
    if (c === '.' && idStart(src[i + 1] || '')) {
      let j = i + 1;
      for (;;) {
        while (j < n && idCont(src[j])) j++;
        if (src[j] === '.' && j + 1 < n && idStart(src[j + 1])) { j++; continue; }
        break;
      }
      push('dotid', src.slice(i + 1, j), i, j); i = j; continue;
    }
    let matched = null;
    for (const s of SYMS) if (src.startsWith(s, i)) { matched = s; break; }
    if (!matched) throw new LeanError(`第 ${line} 行有看不懂的字元「${c}」`, { line });
    push('sym', SYM_ALIAS[matched] || matched, i, i + matched.length);
    i += matched.length;
  }
  toks.push({ t: 'eof', v: '<結尾>', line, col: 0, s: n, e: n, nl: true, adj: false });
  return { toks, comments };
}

/* ───────────── 語法解析 ───────────── */
const BIN = {
  '↔': [20, 21], '→': [25, 25], '∨': [30, 30], '||': [30, 31], '^^': [33, 34], '∧': [35, 35], '&&': [35, 36],
  '=': [50, 51], '≠': [50, 51], '==': [50, 51], '!=': [50, 51], '<': [50, 51], '>': [50, 51], '≤': [50, 51], '≥': [50, 51],
  '+': [65, 66], '-': [65, 66], '*': [70, 71], '/': [70, 71], '%': [70, 71],
};

class Parser {
  constructor(src) {
    this.src = src;
    const r = tokenize(src);
    this.toks = r.toks; this.comments = r.comments;
    this.p = 0; this.cols = [];
    this.enums = new Map(); this.defs = new Map(); this.theorems = [];
    this.ns = []; this.opens = []; this.notes = [];
  }
  peek(k = 0) { return this.toks[Math.min(this.p + k, this.toks.length - 1)]; }
  next() { const t = this.peek(); if (t.t !== 'eof') this.p++; return t; }
  prev() { return this.toks[Math.max(0, this.p - 1)]; }
  is(v, k = 0) { const t = this.peek(k); return (t.t === 'sym' || t.t === 'id') && t.v === v; }
  eat(v) { if (this.is(v)) { this.p++; return true; } return false; }
  expect(v, hint) {
    if (!this.eat(v)) {
      const t = this.peek();
      throw new LeanError(`第 ${t.line} 行：這裡應該出現「${v}」，卻看到「${t.v}」${hint ? '。' + hint : ''}`, t);
    }
  }
  fail(msg, t) { t = t || this.peek(); throw new LeanError(`第 ${t.line} 行：${msg}`, t); }
  isCmdStart(t) {
    if (t.t === 'eof') return true;
    if (!t.nl) return false;
    if (t.t === 'id') return COMMANDS.has(t.v) || t.v[0] === '#';
    return t.t === 'sym' && t.v === '@';
  }
  skipLine() { const ln = this.peek().line; while (this.peek().t !== 'eof' && this.peek().line === ln) this.p++; }
  skipToCmd() { while (!this.isCmdStart(this.peek())) this.p++; }
  skipBalanced() {
    const open = this.next().v, close = { '(': ')', '{': '}', '[': ']' }[open];
    let depth = 1;
    while (depth > 0) {
      const t = this.next();
      if (t.t === 'eof') this.fail(`括號「${open}」沒有對應的「${close}」`, t);
      if (t.t === 'sym' && t.v === open) depth++;
      else if (t.t === 'sym' && t.v === close) depth--;
    }
  }
  qual(name) { return this.ns.length ? this.ns.join('.') + '.' + name : name; }

  parseProgram() {
    for (;;) {
      const t = this.peek();
      if (t.t === 'eof') break;
      if (t.t === 'sym' && t.v === '@') { this.next(); if (this.is('[')) this.skipBalanced(); continue; }
      if (t.t !== 'id') this.fail(`看不懂「${t.v}」。每一段都要以 inductive / def / theorem 開頭`);
      const v = t.v;
      if (v === 'import' || v === 'universe' || v === 'set_option' || v === 'deriving' || v === 'attribute' || v === 'section') { this.skipLine(); continue; }
      if (v[0] === '#') { this.next(); this.skipToCmd(); continue; }
      if (v === 'open') {
        this.next(); const ln = t.line;
        while (this.peek().t === 'id' && this.peek().line === ln && !this.is('in')) this.opens.push(this.next().v);
        this.eat('in'); continue;
      }
      if (v === 'namespace') { this.next(); this.ns.push(this.next().v); continue; }
      if (v === 'end') {
        this.next();
        if (this.peek().t === 'id' && this.peek().line === t.line) { const nm = this.next().v; if (this.ns[this.ns.length - 1] === nm) this.ns.pop(); }
        continue;
      }
      if (v === 'noncomputable' || v === 'private' || v === 'protected') { this.next(); continue; }
      if (v === 'inductive') { this.parseInductive(); continue; }
      if (v === 'def' || v === 'abbrev') { this.parseDef(); continue; }
      if (v === 'theorem' || v === 'lemma' || v === 'example') { this.parseTheorem(); continue; }
      if (v === 'instance') { this.next(); this.skipToCmd(); this.notes.push(`第 ${t.line} 行的 instance 已略過（網頁不需要）`); continue; }
      if (COMMANDS.has(v)) this.fail(`網頁不支援「${v}」。請只用 inductive（列舉型別）、def、theorem 來描述題目`);
      this.fail(`看不懂「${v}」。每一段都要以 inductive / def / theorem 開頭`);
    }
  }

  parseInductive() {
    const kw = this.next();
    const nameTok = this.next();
    if (nameTok.t !== 'id') this.fail('inductive 後面要接型別名稱', nameTok);
    while (!this.is('|') && !this.is('where') && !this.isCmdStart(this.peek())) this.next();
    this.eat('where');
    const ctors = [];
    while (this.is('|')) {
      this.next();
      const c = this.next();
      if (c.t !== 'id') this.fail('「|」後面要接選項名稱', c);
      if (this.is('(') || this.is(':') || this.is('{')) this.fail(`網頁只支援單純的列舉型別，「${c.v}」不能帶參數`);
      ctors.push(c.v);
    }
    if (!ctors.length) this.fail(`型別 ${nameTok.v} 沒有列出任何選項（要寫成 | a | b | c）`, nameTok);
    let e = this.prev().e;
    const derivs = [];
    if (this.is('deriving')) {
      this.next();
      while (this.peek().t === 'id' && !this.isCmdStart(this.peek())) { derivs.push(this.next().v); if (!this.eat(',')) break; }
      e = this.prev().e;
    }
    const name = this.qual(nameTok.v);
    const en = { name, ctors, values: [], s: kw.s, e, derivs, line: kw.line };
    en.values = ctors.map((c, i) => ({ T: name, c, i }));
    this.enums.set(name, en);
  }

  resolveTypeName(name) {
    if (name === 'Bool') return { k: 'bool' };
    if (name === 'Prop') return { k: 'prop' };
    if (name === 'Nat' || name === 'ℕ' || name === 'Int' || name === 'ℤ') return { k: 'nat', name };
    const cands = [name];
    for (let i = this.ns.length; i > 0; i--) cands.push(this.ns.slice(0, i).join('.') + '.' + name);
    for (const o of this.opens) cands.push(o + '.' + name);
    for (const c of cands) if (this.enums.has(c)) return { k: 'enum', name: c };
    return { k: 'other', name };
  }
  parseTypeAtom() {
    const t = this.peek();
    if (t.t === 'sym' && t.v === '(') { this.next(); const ty = this.parseType(); this.expect(')'); return ty; }
    if (t.t !== 'id') this.fail(`這裡應該是型別，卻看到「${t.v}」`);
    this.next();
    if (t.v === 'Fin') {
      const nTok = this.peek();
      if (nTok.t === 'num') { this.next(); return { k: 'fin', n: parseInt(nTok.v, 10) }; }
      return { k: 'other', name: 'Fin' };
    }
    const ty = this.resolveTypeName(t.v);
    if (ty.k === 'other') { // 吃掉型別參數（例如 List Bool）
      while ((this.peek().t === 'id' && !KEYWORDS.has(this.peek().v) && !this.peek().nl) || this.peek().t === 'num') this.next();
    }
    return ty;
  }
  parseType() {
    let ty = this.parseTypeAtom();
    while (this.is('×')) { this.next(); this.parseTypeAtom(); ty = { k: 'other', name: '×' }; }
    if (this.eat('→')) {
      const rest = this.parseType();
      return rest.k === 'fn' ? { k: 'fn', args: [ty, ...rest.args], ret: rest.ret } : { k: 'fn', args: [ty], ret: rest };
    }
    return ty;
  }
  // 試著把接下來的 token 當型別讀；讀不成（或讀完後不是 closer）就回復並回傳 null
  tryType(closer) {
    const save = this.p;
    try {
      const ty = this.parseType();
      if (ty.k !== 'other' && ty.k !== 'fn' && this.is(closer)) return ty;
    } catch (e) { if (!(e instanceof LeanError)) throw e; }
    this.p = save; return null;
  }

  parseBinders(forTheorem) {
    const out = [];
    for (;;) {
      const t = this.peek();
      if (t.t !== 'sym') break;
      if (t.v === '[') { this.skipBalanced(); continue; }
      if (t.v !== '(' && t.v !== '{') break;
      const close = t.v === '(' ? ')' : '}';
      this.next();
      const names = [];
      while (this.peek().t === 'id' && !this.is(':')) names.push(this.next());
      if (!names.length) this.fail('括號裡要先寫名稱，例如 (a b : Bool)');
      this.expect(':');
      const ty = this.tryType(close);
      if (ty) out.push({ kind: 'var', names, type: ty });
      else if (forTheorem) {
        const expr = this.parseExpr(0);
        out.push({ kind: 'hyp', name: names[0].v, expr });
      } else {
        const ty2 = this.parseType();
        out.push({ kind: 'var', names, type: ty2 });
      }
      this.expect(close);
    }
    return out;
  }

  parseDef() {
    const kw = this.next();
    const nameTok = this.next();
    if (nameTok.t !== 'id') this.fail('def 後面要接名稱', nameTok);
    const binders = this.parseBinders(false);
    const params = [];
    for (const b of binders) for (const nm of b.names) params.push({ name: nm.v, type: b.type });
    let retType = null;
    if (this.eat(':')) retType = this.parseType();
    let body;
    if (this.eat(':=')) {
      if (this.is('by')) this.fail('def 的內容不能用 by（策略）寫，請直接寫運算式');
      body = this.parseExpr(0);
    } else if (this.is('|')) {
      const startTok = this.peek();
      const arms = this.parseArms();
      const n = arms[0].alts[0].length;
      const argTypes = retType && retType.k === 'fn' ? retType.args : [];
      const scruts = [];
      for (let i = 0; i < n; i++) {
        const pn = `_arg${i}`;
        params.push({ name: pn, type: argTypes[i] || { k: 'other' } });
        scruts.push({ k: 'id', name: pn, tok: startTok, s: startTok.s, e: startTok.s });
      }
      if (retType && retType.k === 'fn') {
        const rest = retType.args.slice(n);
        retType = rest.length ? { k: 'fn', args: rest, ret: retType.ret } : retType.ret;
      }
      body = { k: 'match', scruts, arms, tok: startTok, s: startTok.s, e: this.prev().e };
    } else this.fail(`def ${nameTok.v} 少了「:=」`);
    const name = this.qual(nameTok.v);
    this.defs.set(name, { name, params, arity: params.length, retType, body, line: kw.line, ns: this.ns.slice(), opens: this.opens.slice(), fn: null, busy: false });
  }

  parseTheorem() {
    const kw = this.next();
    let name = kw.v === 'example' ? `example（第 ${kw.line} 行）` : null;
    if (kw.v !== 'example') {
      const nameTok = this.next();
      if (nameTok.t !== 'id') this.fail('theorem 後面要接名稱', nameTok);
      name = nameTok.v;
    }
    const binders = this.parseBinders(true);
    this.expect(':', 'theorem 的格式是：theorem 名稱 (變數 : 型別) (前提名 : 前提) : 結論 := by decide');
    const stmt = this.parseExpr(0);
    if (!this.is(':=')) {
      const t = this.peek();
      this.fail(`結論讀到「${t.v}」就看不懂了。結論後面要接「:= by decide」`, t);
    }
    this.next();
    const proofS = this.peek().s;
    this.skipToCmd();
    const proofE = this.p > 0 ? this.prev().e : proofS;
    this.theorems.push({ name, kw: kw.v, line: kw.line, binders, stmt, proofS, proofE: Math.max(proofE, proofS), ns: this.ns.slice(), opens: this.opens.slice() });
  }

  /* ── 運算式 ── */
  brk(t) { return t.nl && this.cols.length > 0 && t.col <= this.cols[this.cols.length - 1]; }
  node(n, startTok) { n.tok = n.tok || startTok; n.s = startTok.s; n.e = this.prev().e; return n; }

  parseExpr(minPrec) {
    let left = this.parseUnary();
    for (;;) {
      const t = this.peek();
      if (t.t !== 'sym' || this.brk(t)) break;
      const info = BIN[t.v];
      if (!info || info[0] < minPrec) break;
      this.next();
      const right = this.parseExpr(info[1]);
      left = { k: 'bin', op: t.v, l: left, r: right, tok: t, s: left.s, e: right.e };
    }
    return left;
  }

  parseUnary() {
    const t = this.peek();
    if (t.t === 'sym') {
      if (t.v === '¬' || t.v === '!') { this.next(); const x = this.parseExpr(40); return this.node({ k: 'not', x }, t); }
      if (t.v === '∀' || t.v === '∃' || t.v === '∃!') { this.next(); return this.parseQuant(t, t.v === '∀' ? 'all' : t.v === '∃' ? 'ex' : 'ex1'); }
      if (t.v === 'fun') { this.next(); return this.parseFun(t); }
      if (t.v === '⟨') this.fail('網頁不支援 ⟨ ⟩ 寫法，請改用 ∧ 或分開的變數');
      if (t.v === '-') this.fail('網頁不支援負數');
    }
    if (t.t === 'id') {
      if (t.v === 'forall') { this.next(); return this.parseQuant(t, 'all'); }
      if (t.v === 'exists') { this.next(); return this.parseQuant(t, 'ex'); }
      if (t.v === 'fun') { this.next(); return this.parseFun(t); }
      if (t.v === 'if') {
        this.next();
        if (this.peek().t === 'id' && this.is(':', 1)) { this.next(); this.next(); }
        const c = this.parseExpr(0); this.expect('then');
        const a = this.parseExpr(0); this.expect('else', 'if 一定要有 else');
        const b = this.parseExpr(0);
        return this.node({ k: 'if', c, a, b }, t);
      }
      if (t.v === 'let') {
        this.next();
        const nm = this.next();
        if (nm.t !== 'id') this.fail('let 後面要接名稱', nm);
        let ty = null;
        if (this.eat(':')) ty = this.parseType();
        this.expect(':=');
        this.cols.push(t.col);
        let val; try { val = this.parseExpr(0); } finally { this.cols.pop(); }
        this.eat(';');
        const body = this.parseExpr(0);
        return this.node({ k: 'let', name: nm.v, type: ty, val, body }, t);
      }
      if (t.v === 'match') {
        this.next();
        const scruts = [this.parseExpr(0)];
        while (this.eat(',')) scruts.push(this.parseExpr(0));
        this.expect('with');
        const arms = this.parseArms();
        return this.node({ k: 'match', scruts, arms }, t);
      }
      if (t.v === 'by' || t.v === 'have' || t.v === 'show' || t.v === 'do') this.fail(`這裡不能用「${t.v}」，請直接寫邏輯式`);
    }
    return this.parseApp();
  }

  parseQuant(t, q) {
    const vars = [];
    if (this.is('(')) {
      while (this.is('(')) {
        this.next();
        const names = [];
        while (this.peek().t === 'id' && !this.is(':')) names.push(this.next());
        this.expect(':');
        const ty = this.parseType();
        this.expect(')');
        for (const nm of names) vars.push({ name: nm.v, type: ty, tok: nm });
      }
    } else {
      const names = [];
      while (this.peek().t === 'id' && !KEYWORDS.has(this.peek().v)) names.push(this.next());
      if (!names.length) this.fail(`${t.v} 後面要接變數名稱`);
      if (!this.is(':')) this.fail(`${t.v} 的變數要標型別，例如 ${t.v} x : Bool, …`);
      this.next();
      const ty = this.parseType();
      for (const nm of names) vars.push({ name: nm.v, type: ty, tok: nm });
    }
    this.expect(',');
    const body = this.parseExpr(0);
    return this.node({ k: 'q', q, vars, body }, t);
  }

  parseFun(t) {
    const params = [];
    while (!this.is('=>')) {
      if (this.is('(')) {
        this.next();
        const names = [];
        while (this.peek().t === 'id' && !this.is(':')) names.push(this.next());
        let ty = { k: 'other' };
        if (this.eat(':')) ty = this.parseType();
        this.expect(')');
        for (const nm of names) params.push({ name: nm.v, type: ty });
      } else if (this.peek().t === 'id') {
        params.push({ name: this.next().v, type: { k: 'other' } });
        if (this.is(':')) { this.next(); const ty = this.parseType(); params[params.length - 1].type = ty; }
      } else this.fail('fun 的參數寫法看不懂');
    }
    this.expect('=>');
    const body = this.parseExpr(0);
    return this.node({ k: 'fun', params, body }, t);
  }

  parseArms() {
    const arms = [];
    while (this.is('|')) {
      this.next();
      const alts = [this.parsePatList()];
      while (this.eat('|')) alts.push(this.parsePatList());
      this.expect('=>');
      const body = this.parseExpr(0);
      arms.push({ alts, body });
    }
    if (!arms.length) this.fail('match 後面要有「| 樣式 => 結果」');
    return arms;
  }
  parsePatList() { const ps = [this.parsePat()]; while (this.eat(',')) ps.push(this.parsePat()); return ps; }
  parsePat() {
    const t = this.next();
    if (t.t === 'sym' && t.v === '(') { const p = this.parsePat(); this.expect(')'); return p; }
    if (t.t === 'dotid') return { k: 'ctor', name: t.v, dot: true, tok: t };
    if (t.t === 'num') return { k: 'lit', v: parseInt(t.v, 10), tok: t };
    if (t.t === 'id') {
      if (t.v === '_') return { k: 'wild', tok: t };
      if (t.v === 'true' || t.v === 'false') return { k: 'lit', v: t.v === 'true', tok: t };
      return { k: 'name', name: t.v, tok: t };
    }
    this.fail(`match 的樣式「${t.v}」看不懂（只支援 .選項、true/false、數字、_）`, t);
  }

  canStartAtom(t) {
    if (t.t === 'num') return true;
    if (t.t === 'dotid') return !t.adj;
    if (t.t === 'sym') return t.v === '(';
    if (t.t === 'id') return !KEYWORDS.has(t.v) && !(t.nl && (COMMANDS.has(t.v) || t.v[0] === '#'));
    return false;
  }
  parseApp() {
    const start = this.peek();
    const head = this.parseAtom();
    const args = [];
    for (;;) {
      const t = this.peek();
      if (this.brk(t)) break;
      if (t.t === 'sym' && t.v === '!' && this.canStartAtom(this.peek(1))) {
        this.next(); const x = this.parseAtom(); args.push(this.node({ k: 'not', x }, t)); continue;
      }
      if (!this.canStartAtom(t)) break;
      args.push(this.parseAtom());
    }
    if (!args.length) return head;
    return this.node({ k: 'app', fn: head, args }, start);
  }
  parseAtom() {
    const t = this.next();
    let e;
    if (t.t === 'num') e = this.node({ k: 'num', v: parseInt(t.v, 10) }, t);
    else if (t.t === 'dotid') e = this.node({ k: 'dot', name: t.v }, t);
    else if (t.t === 'id') {
      if (KEYWORDS.has(t.v)) this.fail(`這裡不該出現「${t.v}」`, t);
      e = this.node({ k: 'id', name: t.v }, t);
    } else if (t.t === 'sym' && t.v === '(') {
      const inner = this.parseExpr(0);
      let asc = null;
      if (this.eat(':')) asc = this.parseType();
      if (this.is(',')) this.fail('網頁不支援 (a, b) 這種成對的值，請拆成兩個變數');
      this.expect(')');
      e = inner; e.s = t.s; e.e = this.prev().e;
      if (asc && asc.k === 'enum') e.asc = asc.name;
    } else if (t.t === 'eof') this.fail('內容突然結束了，可能少貼了一段', t);
    else this.fail(`這裡不該出現「${t.v}」`, t);
    while (this.peek().t === 'dotid' && this.peek().adj) {
      const f = this.next();
      e = { k: 'field', x: e, name: f.v, tok: f, s: e.s, e: f.e };
    }
    return e;
  }
}

/* ───────────── 編譯成可執行的函式 ───────────── */
const BUILTINS = {
  'not': [1, a => !a], 'Bool.not': [1, a => !a], 'Not': [1, a => !a], 'decide': [1, a => a], 'id': [1, a => a],
  'and': [2, (a, b) => a && b], 'Bool.and': [2, (a, b) => a && b], 'And': [2, (a, b) => a && b],
  'or': [2, (a, b) => a || b], 'Bool.or': [2, (a, b) => a || b], 'Or': [2, (a, b) => a || b],
  'xor': [2, (a, b) => a !== b], 'Bool.xor': [2, (a, b) => a !== b], 'Xor': [2, (a, b) => a !== b], 'bne': [2, (a, b) => a !== b], 'beq': [2, (a, b) => a === b],
  'Iff': [2, (a, b) => a === b],
  'Bool.toNat': [1, a => (a ? 1 : 0)], 'Fin.val': [1, a => a], 'Nat.succ': [1, a => a + 1], 'Nat.pred': [1, a => Math.max(0, a - 1)],
  'min': [2, Math.min], 'max': [2, Math.max], 'Nat.min': [2, Math.min], 'Nat.max': [2, Math.max],
};
const BOOL_METHODS = { not: 'not', and: 'and', or: 'or', xor: 'xor', toNat: 'Bool.toNat' };

class Compiler {
  constructor(prog) { this.prog = prog; this.used = null; this.track = 0; this.ns = []; this.opens = []; this.warnings = []; }
  err(msg, ast) { const t = ast && (ast.tok || ast); throw new LeanError((t && t.line ? `第 ${t.line} 行：` : '') + msg, t); }

  lookupLocal(scope, name) { for (let i = scope.length - 1; i >= 0; i--) if (scope[i].name === name) return i; return -1; }
  candidates(name) {
    const c = [name];
    for (let i = this.ns.length; i > 0; i--) c.push(this.ns.slice(0, i).join('.') + '.' + name);
    for (const o of this.opens) c.push(o + '.' + name);
    return c;
  }
  // 回傳 {kind:'def',def} | {kind:'val',value,type} | {kind:'builtin',b} | null
  resolveGlobal(name) {
    if (name === 'true' || name === 'True') return { kind: 'val', value: true };
    if (name === 'false' || name === 'False') return { kind: 'val', value: false };
    const { defs, enums } = this.prog;
    for (const c of this.candidates(name)) {
      if (defs.has(c)) return { kind: 'def', def: defs.get(c) };
      const i = c.lastIndexOf('.');
      if (i > 0) {
        const en = enums.get(c.slice(0, i));
        if (en) { const k = en.ctors.indexOf(c.slice(i + 1)); if (k >= 0) return { kind: 'val', value: en.values[k], type: en.name }; }
      }
    }
    if (BUILTINS[name]) return { kind: 'builtin', b: BUILTINS[name], name };
    if (name.indexOf('.') < 0) { // 寬鬆：沒寫型別前綴的選項名，全域唯一就接受
      const hits = [];
      for (const en of enums.values()) { const k = en.ctors.indexOf(name); if (k >= 0) hits.push({ kind: 'val', value: en.values[k], type: en.name }); }
      if (hits.length === 1) return hits[0];
    }
    return null;
  }
  defCall(def) {
    if (def.fn) return def.fn;
    if (def.busy) throw new LeanError(`第 ${def.line} 行：def ${def.name} 呼叫了自己，網頁不支援遞迴定義`, { line: def.line });
    def.busy = true;
    const sNs = this.ns, sOp = this.opens, sUsed = this.used, sTrack = this.track;
    this.ns = def.ns; this.opens = def.opens; this.used = null; this.track = 0;
    try {
      const scope = def.params.map(p => ({ name: p.name, type: p.type }));
      const body = this.compile(def.body, scope, def.retType && def.retType.k === 'enum' ? def.retType.name : null);
      if (def.arity === 0) { let cached, has = false; def.fn = () => { if (!has) { cached = body([]); has = true; } return cached; }; }
      else def.fn = args => body(args);
    } finally { def.busy = false; this.ns = sNs; this.opens = sOp; this.used = sUsed; this.track = sTrack; }
    return def.fn;
  }
  curry(arity, call, sofar) {
    if (sofar.length >= arity) return call(sofar);
    return a => this.curry(arity, call, sofar.concat([a]));
  }

  typeOf(ast, scope) {
    if (!ast) return null;
    if (ast.asc) return ast.asc;
    switch (ast.k) {
      case 'id': {
        const parts = ast.name.split('.');
        const i = this.lookupLocal(scope, parts[0]);
        if (i >= 0) {
          let ty = scope[i].type && scope[i].type.k === 'enum' ? scope[i].type.name : null;
          for (let j = 1; j < parts.length; j++) ty = this.fieldType(ty, parts[j]);
          return ty;
        }
        const g = this.resolveGlobal(ast.name);
        if (!g) return null;
        if (g.kind === 'val') return g.type || null;
        if (g.kind === 'def') return g.def.arity === 0 && g.def.retType && g.def.retType.k === 'enum' ? g.def.retType.name : null;
        return null;
      }
      case 'app': {
        if (ast.fn.k === 'id' && this.lookupLocal(scope, ast.fn.name.split('.')[0]) < 0) {
          const g = this.resolveGlobal(ast.fn.name);
          if (g && g.kind === 'def' && g.def.arity === ast.args.length && g.def.retType && g.def.retType.k === 'enum') return g.def.retType.name;
        }
        return null;
      }
      case 'field': return this.fieldType(this.typeOf(ast.x, scope), ast.name);
      case 'if': return this.typeOf(ast.a, scope) || this.typeOf(ast.b, scope);
      case 'match': return this.typeOf(ast.arms[0].alts.length ? ast.arms[0].body : null, scope);
      default: return null;
    }
  }

  fieldType(tname, field) {
    if (!tname) return null;
    const def = this.prog.defs.get(tname + '.' + field);
    return def && def.arity === 1 && def.retType && def.retType.k === 'enum' ? def.retType.name : null;
  }

  dotCtor(name, exp, ast) {
    const { enums } = this.prog;
    if (exp && enums.has(exp)) { const en = enums.get(exp); const k = en.ctors.indexOf(name); if (k >= 0) return en.values[k]; }
    const hits = [];
    for (const en of enums.values()) { const k = en.ctors.indexOf(name); if (k >= 0) hits.push(en.values[k]); }
    if (hits.length === 1) return hits[0];
    if (!hits.length) this.err(`找不到選項「.${name}」，沒有任何 inductive 型別有這個選項`, ast);
    this.err(`「.${name}」同時是 ${hits.map(h => h.T).join('、')} 的選項，請寫完整名稱（例如 ${hits[0].T}.${name}）`, ast);
  }

  domain(type, ast) {
    if (!type) this.err('變數缺少型別', ast);
    if (type.k === 'bool') return [true, false];
    if (type.k === 'prop') { this.warnings.push('有變數用了 Prop 型別，網頁當成 Bool 處理；建議改寫成 Bool'); return [true, false]; }
    if (type.k === 'enum') return this.prog.enums.get(type.name).values;
    if (type.k === 'fin') {
      if (!(type.n >= 1 && type.n <= 256)) this.err(`Fin ${type.n} 超出範圍，請用 Fin 1 ~ Fin 256`, ast);
      const a = []; for (let i = 0; i < type.n; i++) a.push(i); return a;
    }
    if (type.k === 'nat') this.err(`${type.name} 有無限多個值，沒辦法一一檢查。請改用有範圍的 Fin n（例如 Fin 10 代表 0～9）`, ast);
    if (type.k === 'fn') this.err('變數不能是函式型別，請拆成多個獨立變數', ast);
    this.err(`不認得型別「${type.name || '?'}」。變數只能是 Bool、Fin n，或上面用 inductive 定義的列舉型別`, ast);
  }

  field(base, baseType, name, ast) {
    if (name === 'val' || name === 'toNat' || name === '1') return env => { const v = base(env); return typeof v === 'boolean' ? (v ? 1 : 0) : v; };
    const tname = baseType && baseType.k === 'enum' ? baseType.name : null;
    if (tname) {
      const def = this.prog.defs.get(tname + '.' + name);
      if (def) { const call = this.defCall(def); return env => this.curry(def.arity, call, [base(env)]); }
    }
    if (BOOL_METHODS[name]) { const b = BUILTINS[BOOL_METHODS[name]]; return env => this.curry(b[0], a => b[1](...a), [base(env)]); }
    this.err(`看不懂「.${name}」`, ast);
  }

  compileId(ast, scope) {
    const name = ast.name, parts = name.split('.');
    const li = this.lookupLocal(scope, parts[0]);
    if (li >= 0) {
      if (this.used && li < this.track) this.used.add(li);
      let f = env => env[li], ty = scope[li].type;
      for (let j = 1; j < parts.length; j++) {
        f = this.field(f, ty, parts[j], ast);
        const nt = this.fieldType(ty && ty.k === 'enum' ? ty.name : null, parts[j]);
        ty = nt ? { k: 'enum', name: nt } : null;
      }
      return f;
    }
    const g = this.resolveGlobal(name);
    if (g) {
      if (g.kind === 'val') { const v = g.value; return () => v; }
      if (g.kind === 'def') { const call = this.defCall(g.def); const ar = g.def.arity; return ar === 0 ? () => call([]) : () => this.curry(ar, call, []); }
      const b = g.b; return () => this.curry(b[0], a => b[1](...a), []);
    }
    if (parts.length > 1) {
      const baseAst = { k: 'id', name: parts.slice(0, -1).join('.'), tok: ast.tok };
      const ty = this.typeOf(baseAst, scope);
      let base;
      try { base = this.compileId(baseAst, scope); } catch (e) { base = null; }
      if (base) return this.field(base, ty ? { k: 'enum', name: ty } : null, parts[parts.length - 1], ast);
    }
    this.err(`「${name}」沒有定義。請確認它是變數、def，或 inductive 的選項`, ast);
  }

  compile(ast, scope, exp) {
    switch (ast.k) {
      case 'num': { const v = ast.v; return () => v; }
      case 'dot': { const v = this.dotCtor(ast.name, exp, ast); return () => v; }
      case 'id': return this.compileId(ast, scope);
      case 'field': {
        const ty = this.typeOf(ast.x, scope);
        return this.field(this.compile(ast.x, scope, null), ty ? { k: 'enum', name: ty } : null, ast.name, ast);
      }
      case 'not': { const e = this.compile(ast.x, scope, null); return env => !e(env); }
      case 'if': {
        const c = this.compile(ast.c, scope, null);
        const e2 = exp || this.typeOf(ast.a, scope) || this.typeOf(ast.b, scope);
        const a = this.compile(ast.a, scope, e2), b = this.compile(ast.b, scope, e2);
        return env => (c(env) ? a(env) : b(env));
      }
      case 'let': {
        const slot = scope.length;
        const lt = ast.type && ast.type.k !== 'other' ? ast.type : (t => (t ? { k: 'enum', name: t } : { k: 'other' }))(this.typeOf(ast.val, scope));
        const v = this.compile(ast.val, scope, lt.k === 'enum' ? lt.name : null);
        const body = this.compile(ast.body, scope.concat([{ name: ast.name, type: lt }]), exp);
        return env => { env[slot] = v(env); return body(env); };
      }
      case 'fun': {
        const p = ast.params;
        if (!p.length) return this.compile(ast.body, scope, exp);
        const slot = scope.length;
        const rest = p.length > 1 ? { k: 'fun', params: p.slice(1), body: ast.body, tok: ast.tok } : ast.body;
        const body = this.compile(rest, scope.concat([{ name: p[0].name, type: p[0].type }]), null);
        return env => { const cap = env.slice(0, slot); return a => { const e2 = cap.slice(); e2[slot] = a; return body(e2); }; };
      }
      case 'q': return this.compileQuant(ast, 0, scope);
      case 'match': return this.compileMatch(ast, scope, exp);
      case 'app': return this.compileApp(ast, scope, exp);
      case 'bin': return this.compileBin(ast, scope);
    }
    this.err('看不懂的運算式', ast);
  }

  compileQuant(ast, i, scope) {
    if (i >= ast.vars.length) return this.compile(ast.body, scope, null);
    const v = ast.vars[i], slot = scope.length;
    const dom = this.domain(v.type, v.tok);
    const body = this.compileQuant(ast, i + 1, scope.concat([{ name: v.name, type: v.type }]));
    if (ast.q === 'all') return env => { for (let k = 0; k < dom.length; k++) { env[slot] = dom[k]; if (!body(env)) return false; } return true; };
    if (ast.q === 'ex') return env => { for (let k = 0; k < dom.length; k++) { env[slot] = dom[k]; if (body(env)) return true; } return false; };
    if (ast.vars.length > 1) this.err('∃! 一次只能綁一個變數', ast);
    return env => { let c = 0; for (let k = 0; k < dom.length; k++) { env[slot] = dom[k]; if (body(env) && ++c > 1) return false; } return c === 1; };
  }

  compileMatch(ast, scope, exp) {
    const scr = ast.scruts.map(s => this.compile(s, scope, null));
    const stypes = ast.scruts.map(s => this.typeOf(s, scope));
    const n = scr.length, base = scope.length;
    const bodyExp = exp || this.typeOf(ast.arms[0].body, scope);
    const rows = [];
    for (const arm of ast.arms) {
      for (const pats of arm.alts) {
        if (pats.length !== n) this.err(`match 有 ${n} 個對象，但這一列寫了 ${pats.length} 個樣式`, pats[0].tok);
        const tests = [], binds = [];
        let sc = scope.slice();
        for (let j = 0; j < n; j++) sc.push({ name: '\u0000m' + j, type: null }); // 佔位，讓 slot 對齊
        pats.forEach((p, j) => {
          if (p.k === 'wild') return;
          if (p.k === 'lit') { tests.push([j, p.v]); return; }
          if (p.k === 'ctor') { tests.push([j, this.dotCtor(p.name, stypes[j], p.tok)]); return; }
          // name：是選項就比對，否則當成新變數
          let g = null;
          if (stypes[j]) { const en = this.prog.enums.get(stypes[j]); const short = p.name.split('.').pop(); const k = en.ctors.indexOf(short); if (k >= 0 && (p.name === short || this.resolveGlobal(p.name))) g = en.values[k]; }
          if (!g) { const r = this.resolveGlobal(p.name); if (r && r.kind === 'val' && typeof r.value === 'object') g = r.value; else if (r && r.kind === 'val') { tests.push([j, r.value]); return; } }
          if (g) { tests.push([j, g]); return; }
          binds.push([j, sc.length]);
          const st = ast.scruts[j].k === 'id' ? (() => { const li = this.lookupLocal(scope, ast.scruts[j].name); return li >= 0 ? scope[li].type : null; })() : null;
          sc.push({ name: p.name, type: st });
        });
        rows.push({ tests, binds, body: this.compile(arm.body, sc, bodyExp) });
      }
    }
    const line = ast.tok ? ast.tok.line : '?';
    return env => {
      for (let j = 0; j < n; j++) env[base + j] = scr[j](env);
      outer: for (let r = 0; r < rows.length; r++) {
        const row = rows[r];
        for (let k = 0; k < row.tests.length; k++) if (env[base + row.tests[k][0]] !== row.tests[k][1]) continue outer;
        for (let k = 0; k < row.binds.length; k++) env[row.binds[k][1]] = env[base + row.binds[k][0]];
        return row.body(env);
      }
      throw new LeanError(`第 ${line} 行：match 沒有涵蓋所有情況，請補上「| _ => …」`, { line });
    };
  }

  compileApp(ast, scope, exp) {
    const head = ast.fn;
    if (head.k === 'id' && this.lookupLocal(scope, head.name.split('.')[0]) < 0) {
      const g = this.resolveGlobal(head.name);
      if (g && g.kind === 'val') this.err(`「${head.name}」是一個值，後面不能再接參數`, head);
      if (g && (g.kind === 'def' || g.kind === 'builtin')) {
        const arity = g.kind === 'def' ? g.def.arity : g.b[0];
        const call = g.kind === 'def' ? this.defCall(g.def) : (f => a => f(...a))(g.b[1]);
        const ptypes = g.kind === 'def' ? g.def.params.map(p => (p.type && p.type.k === 'enum' ? p.type.name : null)) : [];
        const args = ast.args.map((a, i) => this.compile(a, scope, ptypes[i] || null));
        const na = args.length;
        if (arity === 0) this.err(`「${head.name}」不接受參數`, head);
        if (na === arity) {
          return env => { const v = new Array(na); for (let i = 0; i < na; i++) v[i] = args[i](env); return call(v); };
        }
        if (na < arity) return env => this.curry(arity, call, args.map(a => a(env)));
        return env => {
          let r = call(args.slice(0, arity).map(a => a(env)));
          for (let i = arity; i < na; i++) { if (typeof r !== 'function') this.err(`「${head.name}」只需要 ${arity} 個參數，這裡給了 ${na} 個`, head); r = r(args[i](env)); }
          return r;
        };
      }
    }
    const f = this.compile(head, scope, null);
    const args = ast.args.map(a => this.compile(a, scope, null));
    return env => {
      let r = f(env);
      for (let i = 0; i < args.length; i++) { if (typeof r !== 'function') this.err('這裡把一個不是函式的東西拿來接參數了（可能少了括號或運算符號）', head); r = r(args[i](env)); }
      return r;
    };
  }

  compileBin(ast, scope) {
    const op = ast.op;
    if (op === '=' || op === '≠' || op === '==' || op === '!=') {
      const tl = this.typeOf(ast.l, scope), tr = this.typeOf(ast.r, scope);
      const l = this.compile(ast.l, scope, tr), r = this.compile(ast.r, scope, tl);
      return op === '=' || op === '==' ? env => l(env) === r(env) : env => l(env) !== r(env);
    }
    if ('+-*/%'.indexOf(op) >= 0) {
      for (const side of [ast.l, ast.r]) {
        if (side.k === 'id') { const li = this.lookupLocal(scope, side.name); if (li >= 0 && scope[li].type && scope[li].type.k === 'fin') this.err(`Fin 變數「${side.name}」做加減乘除時請寫成 ${side.name}.val（否則 Lean 會自動取餘數，結果跟你想的不一樣）`, side); }
      }
    }
    const l = this.compile(ast.l, scope, null), r = this.compile(ast.r, scope, null);
    switch (op) {
      case '∧': case '&&': return env => l(env) && r(env);
      case '∨': case '||': return env => l(env) || r(env);
      case '→': return env => !l(env) || r(env);
      case '↔': return env => l(env) === r(env);
      case '^^': return env => l(env) !== r(env);
      case '<': return env => l(env) < r(env);
      case '>': return env => l(env) > r(env);
      case '≤': return env => l(env) <= r(env);
      case '≥': return env => l(env) >= r(env);
      case '+': return env => l(env) + r(env);
      case '-': return env => Math.max(0, l(env) - r(env));
      case '*': return env => l(env) * r(env);
      case '/': return env => { const b = r(env); return b === 0 ? 0 : Math.floor(l(env) / b); };
      case '%': return env => { const b = r(env); return b === 0 ? l(env) : l(env) % b; };
    }
    this.err(`不支援運算符號「${op}」`, ast);
  }
}

/* ───────────── 定理檢查 ───────────── */
function fmt(v) {
  if (v === true) return 'true';
  if (v === false) return 'false';
  if (typeof v === 'number') return String(v);
  if (v && typeof v === 'object' && v.c) return v.c;
  return '?';
}
function typeLabel(t) {
  if (!t) return '?';
  if (t.k === 'bool') return 'Bool';
  if (t.k === 'prop') return 'Prop';
  if (t.k === 'fin') return 'Fin ' + t.n;
  if (t.k === 'enum') return t.name;
  return t.name || '?';
}
function conjuncts(ast, out) {
  if (ast.k === 'bin' && (ast.op === '∧' || ast.op === '&&')) { conjuncts(ast.l, out); conjuncts(ast.r, out); }
  else out.push(ast);
  return out;
}

function makeLineIndex(src, comments) {
  const starts = [0];
  for (let i = 0; i < src.length; i++) if (src[i] === '\n') starts.push(i + 1);
  const lineOf = off => { let lo = 0, hi = starts.length - 1; while (lo < hi) { const m = (lo + hi + 1) >> 1; if (starts[m] <= off) lo = m; else hi = m - 1; } return lo + 1; };
  const trailing = new Map(), own = new Map();
  for (const c of comments) { if (c.block) continue; (c.own ? own : trailing).set(c.line, c.text); }
  const commentFor = (s, e) => {
    const l1 = lineOf(s), l2 = lineOf(Math.max(s, e - 1));
    return trailing.get(l2) || trailing.get(l1) || own.get(l1 - 1) || '';
  };
  return { lineOf, commentFor };
}

function checkTheorem(prog, comp, thm, src, idx) {
  const vars = [], hyps = [];
  for (const b of thm.binders) {
    if (b.kind === 'var') for (const nm of b.names) vars.push({ name: nm.v, type: b.type, tok: nm, binder: true });
    else hyps.push({ ast: b.expr, name: b.name === '_' ? null : b.name, scopeLen: vars.length, binder: true });
  }
  let stmt = thm.stmt, mode = 'forall';
  for (;;) {
    if (stmt.k === 'q' && stmt.q === 'all') { for (const v of stmt.vars) vars.push({ name: v.name, type: v.type, tok: v.tok }); stmt = stmt.body; }
    else if (stmt.k === 'bin' && stmt.op === '→') { hyps.push({ ast: stmt.l, name: null, scopeLen: vars.length }); stmt = stmt.r; }
    else break;
  }
  let goalAsts = conjuncts(stmt, []);
  if (!vars.length && !hyps.length && stmt.k === 'q' && stmt.q === 'ex') {
    mode = 'exists';
    while (stmt.k === 'q' && stmt.q === 'ex') { for (const v of stmt.vars) vars.push({ name: v.name, type: v.type, tok: v.tok }); stmt = stmt.body; }
    for (const c of conjuncts(stmt, [])) hyps.push({ ast: c, name: null, scopeLen: vars.length });
    goalAsts = [];
  }
  comp.ns = thm.ns; comp.opens = thm.opens;
  const n = vars.length;
  const domains = vars.map(v => comp.domain(v.type, v.tok));
  const scopeAll = vars.map(v => ({ name: v.name, type: v.type }));
  const text = a => src.slice(a.s, a.e).replace(/--[^\n]*/g, '').replace(/\s+/g, ' ').trim();
  const pieces = [];
  hyps.forEach((h, i) => {
    for (const c of conjuncts(h.ast, [])) {
      comp.used = new Set(); comp.track = n;
      const fn = comp.compile(c, scopeAll.slice(0, h.scopeLen), null);
      let level = 0; for (const s of comp.used) level = Math.max(level, s + 1);
      pieces.push({ fn, hyp: i, level, text: text(c) });
    }
  });
  comp.used = null;
  const goals = goalAsts.map(g => ({ fn: comp.compile(g, scopeAll, null), text: text(g), comment: idx.commentFor(g.s, g.e) }));

  const byLevel = []; for (let i = 0; i <= n; i++) byLevel.push([]);
  for (const p of pieces) byLevel[p.level].push(p);
  const suffix = new Array(n + 1); suffix[n] = 1;
  for (let i = n - 1; i >= 0; i--) suffix[i] = suffix[i + 1] * domains[i].length;
  const st = { total: suffix[0], nodes: 0, killed: hyps.map(() => 0), models: 0, good: 0, bad: 0 };
  const models = [], counter = [], trace = [];
  let segs = [];   // [世界數, 代碼]…：代碼 ≥0 = 被第幾個前提排除，-1 = 存活且結論成立，-2 = 存活但結論不成立
  const env = new Array(n);
  let traceKills = 0;
  const rec = d => {
    const ps = byLevel[d];
    for (let k = 0; k < ps.length; k++) {
      st.nodes++;
      if (!ps[k].fn(env)) {
        st.killed[ps[k].hyp] += suffix[d];
        if (segs && segs.length < 60000) segs.push(suffix[d], ps[k].hyp); else segs = null;
        if (traceKills < MAX_TRACE) { traceKills++; trace.push({ d, vals: env.slice(0, d).map(fmt), hyp: ps[k].hyp, piece: ps[k].text, worlds: suffix[d] }); }
        return;
      }
    }
    if (d === n) {
      st.models++;
      let failed = -1;
      for (let j = 0; j < goals.length; j++) if (!goals[j].fn(env)) { failed = j; break; }
      const m = { vals: env.slice(0, n).map(fmt), ok: failed < 0, failed };
      if (segs && segs.length < 60000) segs.push(1, failed < 0 ? -1 : -2); else segs = null;
      if (failed < 0) st.good++; else { st.bad++; if (counter.length < 20) counter.push(m); }
      if (models.length < MAX_MODELS) models.push(m);
      if (st.models <= 80) trace.push({ d, vals: m.vals, hyp: -1, ok: m.ok, failed });
      return;
    }
    if (st.nodes > NODE_LIMIT) throw new LeanError(`可能的情況太多（${st.total.toExponential(1)} 種），瀏覽器檢查不完。請減少變數，或把條件寫得更早能排除情況`, { line: thm.line });
    const dom = domains[d];
    for (let k = 0; k < dom.length; k++) { env[d] = dom[k]; rec(d + 1); }
  };
  try { rec(0); }
  catch (e) { if (e instanceof RangeError) throw new LeanError('計算層數太深（定義可能互相呼叫個不停）', { line: thm.line }); throw e; }

  let verdict;
  if (mode === 'exists') verdict = st.models > 0 ? 'proved' : 'refuted';
  else verdict = st.models === 0 ? 'vacuous' : st.bad === 0 ? 'proved' : 'refuted';

  // 變數分組（顯示用）
  const groups = [];
  for (const v of vars) {
    const lbl = typeLabel(v.type), g = groups[groups.length - 1];
    const cm = idx.commentFor(v.tok.s, v.tok.e);
    if (g && g.type === lbl && g.comment === cm) g.names.push(v.name); else groups.push({ names: [v.name], type: lbl, comment: cm });
  }
  return {
    name: thm.name, kw: thm.kw, line: thm.line, mode, verdict,
    vars: vars.map(v => ({ name: v.name, type: typeLabel(v.type) })), groups,
    hyps: hyps.map((h, i) => ({ label: h.name || `h${i + 1}`, text: text(h.ast), comment: idx.commentFor(h.ast.s, h.ast.e), killed: st.killed[i] })),
    goals: goals.map(g => ({ text: g.text, comment: g.comment })),
    goalText: mode === 'exists' ? text(thm.stmt) : text(stmt),
    stats: st, models, counter, trace, segs,
    revert: { vars: vars.filter(v => v.binder).map(v => v.name), hyps: hyps.filter(h => h.binder && h.name).map(h => h.name) },
  };
}

/* ───────────── 產生可以貼到真正 Lean 4 的完整檔案 ───────────── */
function instancesFor(en) {
  const short = en.name, cs = en.ctors.map(c => `${short}.${c}`), n = cs.length;
  const pc = cs.map(c => `p ${c}`);
  const proj = i => (n === 1 ? 'h' : i === n - 1 ? 'h' + '.2'.repeat(n - 1) : 'h' + '.2'.repeat(i) + '.1');
  const inj = i => { let s = i === n - 1 ? 'h' : 'Or.inl h'; for (let k = 0; k < Math.min(i, n - 1); k++) s = `Or.inr (${s})`; return n === 1 ? 'h' : s; };
  let elim = 'fun h => ⟨_, h⟩';
  for (let i = n - 2; i >= 0; i--) elim = `fun h => h.elim (fun h => ⟨_, h⟩) (${elim})`;
  return [
    `instance (p : ${short} → Prop) [DecidablePred p] : Decidable (∀ x, p x) :=`,
    `  decidable_of_iff (${pc.join(' ∧ ')})`,
    `    ⟨fun h x => by cases x; ${cs.map((_, i) => `exact ${proj(i)}`).join('; ')},`,
    `     fun h => ⟨${cs.map(c => `h ${c}`).join(', ')}⟩⟩`,
    `instance (p : ${short} → Prop) [DecidablePred p] : Decidable (∃ x, p x) :=`,
    `  decidable_of_iff (${pc.join(' ∨ ')})`,
    `    ⟨${elim},`,
    `     fun ⟨x, h⟩ => by cases x; ${cs.map((_, i) => `exact ${inj(i)}`).join('; ')}⟩`,
  ].join('\n');
}

function exportLean(src, prog, results) {
  const edits = [];
  for (const en of prog.enums.values()) {
    if (en.derivs.indexOf('Fintype') >= 0) continue;
    let ins = '';
    if (en.derivs.indexOf('DecidableEq') < 0) ins += (en.derivs.length ? ', DecidableEq' : '\n  deriving DecidableEq');
    ins += '\n\n-- ↓ 網頁自動補上：讓 Lean 知道這個型別只有這幾個選項，可以逐一檢查\n' + instancesFor(en);
    edits.push({ s: en.e, e: en.e, text: ins });
  }
  prog.theorems.forEach((thm, i) => {
    const r = results[i];
    let proof = 'by decide';
    if (r && r.revert && (r.revert.vars.length || r.revert.hyps.length)) {
      const lines = [];
      if (r.revert.hyps.length) lines.push('  revert ' + r.revert.hyps.join(' '));
      if (r.revert.vars.length) lines.push('  revert ' + r.revert.vars.join(' '));
      proof = 'by\n' + lines.join('\n') + '\n  decide';
    }
    edits.push({ s: thm.proofS, e: thm.proofE, text: proof });
  });
  let pos = 0; const re = /^[ \t]*import[^\n]*\n?/gm; let m;
  while ((m = re.exec(src))) pos = m.index + m[0].length;
  edits.push({ s: pos, e: pos, text: 'set_option maxRecDepth 100000\n\n' });
  edits.sort((a, b) => b.s - a.s);
  let out = src;
  for (const ed of edits) out = out.slice(0, ed.s) + ed.text + out.slice(ed.e);
  return out;
}

/* ───────────── 對外介面 ───────────── */
function extractMeta(raw, comments) {
  const meta = { title: '', conclusion: '', cannot: '' };
  const grab = (text, tag) => {
    const i = text.indexOf('【' + tag + '】');
    if (i < 0) return '';
    let rest = text.slice(i + tag.length + 2);
    const j = rest.indexOf('【');
    if (j >= 0) rest = rest.slice(0, j);
    return rest.replace(/^\s*[:：]?\s*/, '').replace(/-\/\s*$/, '').replace(/```[\s\S]*$/, '').replace(/^\s*--\s?/gm, '').trim();
  };
  // 一個註解一個註解找，標籤內容不會吃到後面別的註解
  const find = tag => { for (const c of comments) { const r = grab(c.text, tag); if (r) return r; } return ''; };
  meta.title = find('題目');
  meta.conclusion = find('結論');
  meta.cannot = find('無法轉換') || grab(raw, '無法轉換');
  meta.suggest = find('建議改法') || grab(raw, '建議改法');
  if (!meta.cannot && /【無法轉換】/.test(raw)) meta.cannot = '（AI 沒有說明原因）';
  return meta;
}

// AI 常把程式包在 ```lean … ``` 裡；只取第一個程式區塊
function cleanSource(raw) {
  const m = /```[a-zA-Z0-9]*[ \t]*\n([\s\S]*?)```/.exec(raw);
  let s = m ? m[1] : raw;
  s = s.replace(/\r\n/g, '\n').replace(/[​‌‍]/g, '');
  return s.replace(/^\n+/, '').replace(/\s+$/, '') + '\n';
}

function check(raw) {
  const src = cleanSource(raw || '');
  const out = { ok: false, src, meta: { title: '', conclusion: '', cannot: '' }, theorems: [], error: null, notes: [], exportLean: '' };
  if (!src.trim()) { out.error = { msg: '還沒有貼上任何內容' }; return out; }
  let parser;
  try {
    parser = new Parser(src);
    out.meta = extractMeta(raw, parser.comments);
    if (out.meta.cannot && !/\b(theorem|example|lemma)\b/.test(src.replace(/\/-[\s\S]*?-\//g, '').replace(/--[^\n]*/g, ''))) { out.cannot = true; return out; }
    parser.parseProgram();
  } catch (e) {
    if (!(e instanceof LeanError)) throw e;
    try { out.meta = extractMeta(raw, tokenizeSafe(src)); } catch (_) { /* 忽略 */ }
    if (/【無法轉換】/.test(raw)) { out.meta.cannot = out.meta.cannot || '（AI 沒有說明原因）'; out.cannot = true; return out; }
    out.error = { msg: e.message, line: e.line }; return out;
  }
  out.notes = parser.notes.slice();
  if (!parser.theorems.length) {
    if (out.meta.cannot) { out.cannot = true; return out; }
    out.error = { msg: '裡面沒有 theorem。要檢查的結論必須寫成「theorem 名稱 … : 結論 := by decide」' }; return out;
  }
  const comp = new Compiler(parser);
  const idx = makeLineIndex(src, parser.comments);
  for (const thm of parser.theorems) {
    try { out.theorems.push(checkTheorem(parser, comp, thm, src, idx)); }
    catch (e) {
      if (!(e instanceof LeanError)) throw e;
      out.theorems.push({ name: thm.name, kw: thm.kw, line: thm.line, verdict: 'error', error: { msg: e.message, line: e.line || thm.line } });
    }
  }
  for (const w of new Set(comp.warnings)) out.notes.push(w);
  out.ok = true;
  out.enums = Array.from(parser.enums.values()).map(e => ({ name: e.name, ctors: e.ctors }));
  out.exportLean = exportLean(src, parser, out.theorems);
  return out;
}
function tokenizeSafe(src) { try { return tokenize(src).comments; } catch (e) { return []; } }

const api = { check, cleanSource, LeanError };
if (typeof module !== 'undefined' && module.exports) module.exports = api;
else root.LeanEngine = api;
})(typeof window !== 'undefined' ? window : globalThis);
