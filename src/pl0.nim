import std/options
import std/tables
import std/syncio
import std/cmdline
from std/strutils import parseInt
from std/strformat import `&`
from std/enumerate import enumerate

type
  ExprType = enum
    E_BINOP
    E_UNARYOP
    E_LIT
    E_VAR
  Expr = ref object
    line: int
    col: int
    case eType: ExprType
    of E_BINOP:
      binop: string
      bLhs: Expr
      bRhs: Expr
    of E_UNARYOP:
      uOp: string
      uBody: Expr
    of E_LIT:
      lVal: int
    of E_VAR:
      vName: string
  CondType = enum
    C_EXPR_PRED
    C_EXPR_REL
  Cond = ref object
    line: int
    col: int
    case cType: CondType
    of C_EXPR_PRED:
      predName: string
      pBody: Expr
    of C_EXPR_REL:
      relOp: string
      relLhs: Expr
      relRhs: Expr
  StatementType = enum
    S_ASSIGN
    S_CALL
    S_INPUT
    S_PRINT
    S_BLOCK
    S_IF
    S_WHILE
  Statement = ref object
    line: int
    col: int
    case sType: StatementType
    of S_ASSIGN:
      aTarget: string
      aVal: Expr
    of S_CALL:
      cTarget: string
    of S_INPUT:
      iTarget: string
    of S_PRINT:
      pExpr: Expr
    of S_BLOCK:
      body: seq[Statement]
    of S_IF:
      ifCond: Cond
      ifThen: Statement
    of S_WHILE:
      wCond: Cond
      wBody: Statement
  Block = ref object
    line: int
    col: int
    constDef: seq[(string, int)]
    varDef: seq[string]
    procDef: seq[(string, Block)]
    body: Statement
  Program = ref object
    body: Block

type
  ParserState = ref object
    line: int
    col: int
    x: string
    stp: int

let reservedWords: seq[string] = @[
  "if", "then", "while", "do", "begin", "end", "procedure", "const", "var", "input", "print"
]

proc raiseErrorWithReason(x: ParserState, reason: string): void =
  raise newException(ValueError, &"[Parser] ({x.line},{x.col}) {reason}")
proc raiseErrorWithReason(x: Expr, reason: string): void =
  raise newException(ValueError, &"[Compiler] ({x.line},{x.col}) {reason}")
proc raiseErrorWithReason(x: Cond, reason: string): void =
  raise newException(ValueError, &"[Compiler] ({x.line},{x.col}) {reason}")
proc raiseErrorWithReason(x: Statement, reason: string): void =
  raise newException(ValueError, &"[Compiler] ({x.line},{x.col}) {reason}")
proc raiseErrorWithReason(x: Block, reason: string): void =
  raise newException(ValueError, &"[Compiler] ({x.line},{x.col}) {reason}")

proc isDigit(x: char): bool {.inline.} =
  '0' <= x and x <= '9'
proc isNameHeadChar(x: char): bool {.inline.} =
  ('a' <= x and x <= 'z') or ('A' <= x and x <= 'Z') or x == '_'
proc isNameChar(x: char): bool {.inline.} =
  x.isDigit or x.isNameHeadChar

proc takeIdent(x: ParserState): Option[string] =
  var i = x.stp
  let lenx = x.x.len
  if i < lenx and x.x[i].isNameHeadChar: i += 1
  else: return none(string)
  while i < lenx and x.x[i].isNameChar: i += 1
  let name = x.x[x.stp..<i]
  if name in reservedWords: return none(string)
  x.col += i-x.stp
  x.stp = i
  return some(name)

proc takeInteger(x: ParserState): Option[int] =
  var i = x.stp
  let lenx = x.x.len
  if i < lenx and x.x[i].isDigit: i += 1
  else: return none(int)
  while i < lenx and x.x[i].isDigit: i += 1
  let name = x.x[x.stp..<i]
  x.col += i-x.stp
  x.stp = i
  return some(name.parseInt)
  
proc skipWhite(x: ParserState): ParserState =
  var i = x.stp
  let lenx = x.x.len
  while i < lenx and x.x[i] in " \n\r\v\t\b\f":
    if x.x[i] in "\n\v\f":
      x.line += 1
      x.col = 0
    else:
      x.col += 1
    i += 1
  x.stp = i
  return x

proc expect(x: ParserState, pat: string): Option[string] =
  let lenx = x.x.len
  if lenx-x.stp < pat.len: return none(string)
  let prefix = x.x[x.stp..<x.stp+pat.len]
  if prefix != pat: return none(string)
  for i in pat:
    if i in "\n\v\f":
      x.line += 1
      x.col = 0
    else:
      x.col += 1
  x.stp += pat.len
  return some(pat)

proc peek(x: ParserState, pat: string): bool = 
  let lenx = x.x.len
  if lenx-x.stp < pat.len: return false
  let prefix = x.x[x.stp..<x.stp+pat.len]
  if prefix != pat: return false
  return true

proc parseExpr(x: ParserState): Option[Expr]
proc parseFactor(x: ParserState): Option[Expr] =
  let z1 = x.skipWhite().takeIdent()
  if z1.isSome(): return some(Expr(line: x.line, col: x.col, eType: E_VAR, vName: z1.get()))
  let z2 = x.skipWhite().takeInteger()
  if z2.isSome(): return some(Expr(line: x.line, col: x.col, eType: E_LIT, lVal: z2.get()))
  if x.skipWhite.expect("(").isNone(): return none(Expr)
  let z3 = x.skipWhite.parseExpr()
  if z3.isNone(): x.raiseErrorWithReason("Expression expected.")
  if x.skipWhite.expect(")").isNone(): x.raiseErrorWithReason("Right parenthesis expected.")
  return z3

proc parseTerm(x: ParserState): Option[Expr] =
  var res = x.skipWhite.parseFactor
  if res.isNone(): return none(Expr)
  while true:
    var thisOp = x.skipWhite.expect("*")
    if thisOp.isNone(): thisOp = x.skipWhite.expect("/")
    if thisOp.isNone(): return res
    var rhs = x.skipWhite.parseFactor
    if rhs.isNone(): x.raiseErrorWithReason("Term expected.")
    res = some(Expr(line: x.line, col: x.col, eType: E_BINOP, binop: thisOp.get(), bLhs: res.get(), bRhs: rhs.get()))
    continue

proc parseExpr(x: ParserState): Option[Expr] =
  var prefixUnaryOp = x.skipWhite.expect("+")
  if prefixUnaryOp.isNone(): prefixUnaryOp = x.skipWhite.expect("-")
  var res = x.skipWhite.parseTerm
  if res.isNone():
    if prefixUnaryOp.isNone(): return none(Expr)
    else: x.raiseErrorWithReason("Term expected.")
  if prefixUnaryOp.isSome():
    res = some(Expr(line: x.line, col: x.col, eType: E_UNARYOP, uOp: prefixUnaryOp.get(), uBody: res.get()))
  while true:
    var thisOp = x.skipWhite.expect("+")
    if thisOp.isNone(): thisOp = x.skipWhite.expect("-")
    if thisOp.isNone(): return res
    var rhs = x.skipWhite.parseTerm
    if rhs.isNone(): x.raiseErrorWithReason("Term expected.")
    res = some(Expr(line: x.line, col: x.col, eType: E_BINOP, binop: thisOp.get(), bLhs: res.get(), bRhs: rhs.get()))
    continue

proc parseCond(x: ParserState): Option[Cond] =
  var shouldBePred = x.skipWhite.expect("odd")
  if shouldBePred.isSome():
    var body = x.skipWhite.parseExpr
    if body.isNone(): x.raiseErrorWithReason("Expression expected.")
    return some(Cond(line: x.line, col: x.col, cType: C_EXPR_PRED, predName: shouldBePred.get(), pBody: body.get()))
  var lhs = x.skipWhite.parseExpr
  if lhs.isNone(): return none(Cond)
  var thisOp = x.skipWhite.expect("=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("#")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("<=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect("<")
  if thisOp.isNone(): thisOp = x.skipWhite.expect(">=")
  if thisOp.isNone(): thisOp = x.skipWhite.expect(">")
  if thisOp.isNone(): x.raiseErrorWithReason("Expression expected.")
  var rhs = x.skipWhite.parseExpr
  if rhs.isNone(): x.raiseErrorWithReason("Expression expected.")
  return some(Cond(line: x.line, col: x.col, cType: C_EXPR_REL, relOp: thisOp.get(), relLhs: lhs.get(), relRhs: rhs.get()))

proc parseStatement(x: ParserState): Option[Statement] =
  if x.skipWhite.peek("call"):
    discard x.skipWhite.expect("call")
    var target = x.skipWhite.takeIdent()
    if target.isNone(): x.raiseErrorWithReason("Identifier expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_CALL, cTarget: target.get()))
  if x.skipWhite.peek("input"):
    discard x.skipWhite.expect("input")
    var target = x.skipWhite.takeIdent()
    if target.isNone(): x.raiseErrorWithReason("Identifier expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_INPUT, iTarget: target.get()))
  if x.skipWhite.peek("print"):
    discard x.skipWhite.expect("print")
    var target = x.skipWhite.parseExpr()
    if target.isNone(): x.raiseErrorWithReason("Expression expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_PRINT, pExpr: target.get()))
  if x.skipWhite.peek("begin"):
    discard x.skipWhite.expect("begin")
    var body: seq[Statement] = @[]
    var thisStmt = x.skipWhite.parseStatement
    if thisStmt.isNone(): x.raiseErrorWithReason("Statement expected.")
    body.add(thisStmt.get())
    # NOTE: this is slightly different from the original PL/0: here we allow
    # empty statements too.
    while not x.skipWhite.peek("end"):
      var sep = x.expect(";")
      if sep.isNone(): x.raiseErrorWithReason("Statement, semicolon or \"end\" expected.")
      var nextStatement = none(Statement)
      try:
        nextStatement = x.skipWhite.parseStatement
      except:
          discard
      if nextStatement.isNone(): continue
      body.add(nextStatement.get())
    if x.skipWhite.expect("end").isNone(): x.raiseErrorWithReason("\"end\" expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_BLOCK, body: body))
  if x.skipWhite.peek("if"):
    discard x.skipWhite.expect("if")
    var cond = x.skipWhite.parseCond
    if cond.isNone(): x.raiseErrorWithReason("Condition expected.")
    if x.skipWhite.expect("then").isNone(): x.raiseErrorWithReason("\"then\" expected.")
    var body = x.skipWhite.parseStatement
    if body.isNone(): x.raiseErrorWithReason("Statement expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_IF, ifCond: cond.get(), ifThen: body.get()))
  if x.skipWhite.peek("while"):
    discard x.skipWhite.expect("while")
    var cond = x.skipWhite.parseCond
    if cond.isNone(): x.raiseErrorWithReason("Condition expected.")
    if x.skipWhite.expect("do").isNone(): x.raiseErrorWithReason("\"do\" expected.")
    var body = x.skipWhite.parseStatement
    if body.isNone(): x.raiseErrorWithReason("Statement expected.")
    return some(Statement(line: x.line, col: x.col, sType: S_WHILE, wCond: cond.get(), wBody: body.get()))
  var ident = x.skipWhite.takeIdent()
  if ident.isNone(): x.raiseErrorWithReason("Identifier (or any of the statement keyword) expected.")
  if x.skipWhite.expect(":=").isNone(): x.raiseErrorWithReason("\":=\" expected.")
  var rhs = x.skipWhite.parseExpr
  if rhs.isNone(): x.raiseErrorWithReason("Expression expected.")
  return some(Statement(line: x.line, col: x.col, sType: S_ASSIGN, aTarget: ident.get(), aVal: rhs.get()))

proc parseConstClause(x: ParserState): Option[seq[(string, int)]] =
  if x.expect("const").isNone(): return none(seq[(string, int)])
  var firstIdent = x.skipWhite.takeIdent
  if firstIdent.isNone(): x.raiseErrorWithReason("Identifier expected.")
  if x.skipWhite.expect("=").isNone(): x.raiseErrorWithReason("\"=\" expected.")
  var firstNumber = x.skipWhite.takeInteger
  if firstNumber.isNone(): x.raiseErrorWithReason("Integer expected.")
  var res: seq[(string, int)] = @[(firstIdent.get(), firstNumber.get())]
  while true:
    if x.skipWhite.expect(",").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    if x.skipWhite.expect("=").isNone(): x.raiseErrorWithReason("\"=\" expected.")
    var number = x.skipWhite.takeInteger
    if number.isNone(): x.raiseErrorWithReason("Integer expected.")
    res.add((ident.get(), number.get()))
  if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
  return some(res)

proc parseVarClause(x: ParserState): Option[seq[string]] =
  if x.skipWhite.expect("var").isNone(): return none(seq[string])
  var firstIdent = x.skipWhite.takeIdent
  if firstIdent.isNone(): x.raiseErrorWithReason("Identifier expected.")
  var res: seq[string] = @[firstIdent.get()]
  while true:
    if x.skipWhite.expect(",").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    res.add(ident.get())
  if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
  return some(res)

proc parseBlock(x: ParserState): Option[Block]
proc parseProcClause(x: ParserState): Option[seq[(string, Block)]] =
  var res: seq[(string, Block)] = @[]
  while true:
    if x.skipWhite.expect("procedure").isNone(): break
    var ident = x.skipWhite.takeIdent
    if ident.isNone(): x.raiseErrorWithReason("Identifier expected.")
    if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
    var blockRes = x.skipWhite.parseBlock
    if blockRes.isNone(): x.raiseErrorWithReason("Block expected.")
    if x.skipWhite.expect(";").isNone(): x.raiseErrorWithReason("\";\" expected.")
    res.add((ident.get(), blockRes.get()))
  return some(res)
  
proc parseBlock(x: ParserState): Option[Block] =
  var constClause = x.skipWhite.parseConstClause
  var varClause = x.skipWhite.parseVarClause
  var procClause = x.skipWhite.parseProcClause
  var body = x.skipWhite.parseStatement
  if body.isNone(): x.raiseErrorWithReason("Statement expected.")
  return some(Block(line: x.line, col: x.col,
                    constDef: if constClause.isNone(): @[] else: constClause.get(),
                    varDef: if varClause.isNone(): @[] else: varClause.get(),
                    procDef: if procClause.isNone(): @[] else: procClause.get(),
                    body: body.get()))

proc parseProgram(x: ParserState): Option[Program] =
  var blockRes = x.skipWhite.parseBlock
  if x.skipWhite.expect(".").isNone(): x.raiseErrorWithReason("\".\" expected.")
  return some(Program(body: blockRes.get()))

proc parseProgram(x: string): Option[Program] =
  ParserState(line: 0, col: 0, x: x, stp: 0).parseProgram

# compiler.
type
  InstrType = enum
    LIT
    OPR
    LOD
    STO
    CAL
    INT
    JMP
    JPC
  Instr = (InstrType, int, int)

proc `$`(x: InstrType): string =
  case x:
    of LIT: "LIT"
    of OPR: "OPR"
    of LOD: "LOD"
    of STO: "STO"
    of CAL: "CAL"
    of INT: "INT"
    of JMP: "JMP"
    of JPC: "JPC"

proc collectConst(x: Block): TableRef[string, int] =
  var res = newTable[string, int]()
  for v in x.constDef:
    res[v[0]] = v[1]
  return res

# The idea of this part goes as follows:
# When the compiler descends into the nesting procedure
# is maintained; one can get the "layer offset" by subtracting layer count and
# variable base even if everything is strictly increasing; to see why "increasing"
# would be a problem, consider the following example:
#
#     procedure A;
#       var a;  (* Considered base 0 *)
#       procedure B;
#         var b;  (* Considered base 1 *)
#         procedure C;
#           var c;  (* Considered base 2 *)
#           procedure D;
#             var d;  (* Considered base 3 *)
#           begin
#             a := c + d;  (* point A *)
#           end;
#         begin
#           a := b + c;  (* point B *)
#         end;
#       begin
#         a := a + b;  (* point C *)
#       end;
#     ...
#
# Due to how the vm works and how the stack frame is laid out, the way the
# variable `a` should be referred to is different between point A, B and C:
# at point A, `a` should be `STO 3, 0`; at point B, `a` should be `STO 2, 0`;
# at point C, `a` should be `STO 1, 0`. If we choose to build the location
# mapping as we descent, we'll need to change the layer count every time we
# descend a layer; this may not be too big of a problem since deeply-nested
# procedures are rare, but it's troublesome and prone to err to do this.
# If we maintain a "layer count" variable as we descend, variables
# like `a`, `b`, `c` and `d` can simply be `(0, 0)`, `(1, 0)`, `(2, 0)`
# and `(3, 0)` and one can retrieve the correct layer count for `LOD` and `STO`
# anytime by subtracting the base from the layer count variable, e.g. at
# point A the layer count is 3 (starts from 0) and one can get the base for `a`
# by `3-0 = 3` and the base for c by `3-2 = 1`.

type
  # this field is defined as a seq for easy maintaining between many nested
  # procedures.
  EnvFrame = tuple
    constTable: TableRef[string, int]
    varTable: TableRef[string, (int, int)]
    procTable: TableRef[string, int]
  Env = seq[EnvFrame]
  
proc allocVar(x: Block, base: int): TableRef[string, (int, int)] =
  var res = newTable[string, (int, int)]()
  for (i, v) in enumerate(x.varDef):
    res[v] = (base, i)
  return res

# NOTE: this returns "resolved location", i.e. the one you directly plugs
# into `STO` and `LOD`.
proc lookupVar(name: string, layerCount: int, env: Env): Option[(int, int)] =
  assert(layerCount == env.len()-1)
  var i = env.len()-1
  while i >= 0:
    let t = env[i].varTable
    if t == nil:
      i -= 1
      continue
    if not t.hasKey(name):
      i -= 1
      continue
    return some((layerCount-i, t[name][1]))
  return none((int, int))

proc lookupConst(name: string, env: Env): Option[int] =
  var i = env.len()-1
  while i >= 0:
    let t = env[i].constTable
    if t == nil:
      i -= 1
      continue
    if not t.hasKey(name):
      i -= 1
      continue
    return some(t[name])
  return none(int)

proc compileExpr(x: Expr, layerCount: int, env: Env): seq[Instr] =
  var res: seq[Instr] = @[]
  case x.eType:
    of E_BINOP:
      res &= x.bLhs.compileExpr(layerCount, env)
      res &= x.bRhs.compileExpr(layerCount, env)
      let opNum = case x.binop:
                    of "+": 2
                    of "-": 3
                    of "*": 4
                    of "/": 5
                    else: -1  # cannot happen
      res.add((OPR, 0, opNum))
    of E_UNARYOP:
      res &= x.uBody.compileExpr(layerCount, env)
      let opNum = case x.uOp:
                    of "-": 1
                    else: -1  # cannot happend
      res.add((OPR, 0, opNum))
    of E_LIT:
      res.add((LIT, 0, x.lVal))
    of E_VAR:
      var lookupRes = lookupVar(x.vName, layerCount, env)
      if lookupRes.isSome():
        res.add((LOD, lookupRes.get()[0], lookupRes.get()[1]))
      else:
        let constLookupRes = lookupConst(x.vName, env)
        if constLookupRes.isSome():
          res.add((LIT, 0, constLookupRes.get()))
        else:
          x.raiseErrorWithReason(&"Cannot find the definition of {x.vName}")
  return res

proc compileCond(x: Cond, layerCount: int, env: Env): seq[Instr] =
  var res: seq[Instr] = @[]
  case x.cType:
    of C_EXPR_PRED:
      res &= x.pBody.compileExpr(layerCount, env)
      let opNum = case x.predName:
                    of "odd": 6
                    else: -1
      res.add((OPR, 0, opNum))
    of C_EXPR_REL:
      res &= x.relLhs.compileExpr(layerCount, env)
      res &= x.relRhs.compileExpr(layerCount, env)
      let opNum = case x.relOp:
                    of "=": 8
                    of "#": 9
                    of "<=": 11
                    of ">=": 13
                    of "<": 10
                    of ">": 12
                    else: -1  # cannot happen
      res.add((OPR, 0, opNum))
  return res

# Now this gets slightly tricky. The branching instruction in the vm of the original
# PL/0 uses absolute address while it's more common to have offsets for branching
# instructions. To compile things with absolute address we need to know the actual
# location of a lot of things. Consider this example:
#
#   if a > 3 then
#   begin
#     a := 3;
#   end;
#
# One shall compile this into:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       LIT 0, 3
#       STO (a)
#   L1:
#
# (Notice that JPC jumps when the stacktop is 0, i.e. condition not satisfied)
# If JPC takes an offset as its argument then it can be resolved recursively
# without knowing where exactly L1 would be, since the offset would be only
# related to the length of the branch body. Also consider this example:
#
#   while a < 5 do
#   begin
#     a := a + 2;
#   end;
#
# This shall be compiled into:
#
#   L1: LOD (a)
#       LIT 0, 5
#       OPR 0, 10
#       JPC 0, L2
# 
#       LOD (a)
#       LIT 0, 2
#       OPR 0, 2
#       STO (a)
#       JMP 0, L1
#   L2:
#
# Not only do we need to know where L2 is, we also need to know where L1 is now. 

# Now I shall explain why the return type is (seq[Instr], seq[int]): this is to
# support mutual recursion. To compile a CALL statement that refers to a
# procedure that happens later in the source code, one must first know its
# location; but to know its location we must compile everything because we need
# to do that to work out the size and from the size the location; it's a mutual
# dependent situation. The solution taken here is to first compile everything
# but with placeholder CAL instructions and to fill in the actual value later.
# the `seq[(int, int, string)]` part is for returning the location of such
# instructions and the name of the called procedures. The second `int` part is
# to maintain the proper layer count; this will become relevant in later parts.
proc compileStatementList(x: seq[Statement], currentLoc: int, layerCount: int, env: Env): (seq[Instr], seq[(int, int, string)])
proc compileStatement(x: Statement, currentLoc: int, layerCount: int, env: Env): (seq[Instr], seq[(int, int, string)]) =
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  case x.sType:
    of S_ASSIGN:
      let resolveRes = lookupVar(x.aTarget, layerCount, env)
      if resolveRes.isNone(): x.raiseErrorWithReason(&"Variable name {x.aTarget} not found.")
      res &= x.aVal.compileExpr(layerCount, env)
      res.add((STO, resolveRes.get()[0], resolveRes.get()[1]))
    of S_BLOCK:
      let s = compileStatementList(x.body, currentLoc, layerCount, env)
      res &= s[0]
      callFillers &= s[1]
    of S_IF:
      let condPart: seq[Instr] = compileCond(x.ifCond, layerCount, env)
      res &= condPart
      # the `+1` is for the JPC instr itself; it's the same case for S_WHILE.
      let bodyPart = compileStatement(x.ifThen, currentLoc + condPart.len + 1, layerCount, env)
      let bodyInstr = bodyPart[0]
      let bodyCallFillers = bodyPart[1]
      res.add((JPC, 0, currentLoc + condPart.len() + 1 + bodyInstr.len()))
      res &= bodyInstr
      callFillers &= bodyCallFillers
    of S_WHILE:
      let l1 = currentLoc
      let condPart = compileCond(x.wCond, layerCount, env)
      res &= condPart
      let bodyPart = compileStatement(x.wBody, currentLoc + condPart.len + 1, layerCount, env)
      # the last `+1` part is for the JMP instruction used to jump back to L1.
      res.add((JPC, 0, currentLoc + condPart.len + 1 + bodyPart[0].len + 1))
      res &= bodyPart[0]
      res.add((JMP, 0, l1))
      callFillers &= bodyPart[1]
    of S_INPUT:
      let resolveRes = lookupVar(x.iTarget, layerCount, env)
      if resolveRes.isNone(): x.raiseErrorWithReason(&"Variable name {x.iTarget} not found")
      res.add((OPR, 0, 7))
      res.add((STO, resolveRes.get()[0], resolveRes.get()[1]))
    of S_PRINT:
      res &= compileExpr(x.pExpr, layerCount, env)
      res.add((OPR, 0, 14))
    of S_CALL:
      # inserting placeholder call instr.
      res.add((CAL, 0, 0))
      callFillers.add((currentLoc, 0, x.cTarget))
  return (res, callFillers)

proc compileStatementList(x: seq[Statement], currentLoc: int, layerCount: int, env: Env): (seq[Instr], seq[(int, int, string)]) =
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  var cnt = currentLoc
  for stmt in x:
    let stmtRes = stmt.compileStatement(cnt, layerCount, env)
    res &= stmtRes[0]
    callFillers &= stmtRes[1]
    cnt += stmtRes[0].len()
  return (res, callFillers)

# For every block we need to do the following things:
# 1.  Collect all constant definitions.
# 2.  Allocate variables.
# 3.  Compile all local procedures.
# 4.  Compile block body.
# The layout of the generated insructions would be:
#
#       INT 0, (size)
#       JMP 0, L1
#       (proc 1)
#       (proc 2)
#       (...)
#   L1: (body)
#       OPR 0, 0
#
# From this we know to insert the JMP instruction at the beginning we must know
# the proper location of L1; thus we need to first compile the local procedures
# first.
#
# Now this is very tricky. Do we allow local procedures calling other
# procedures defined in the "outside"? If so, we cannot truly resolve all the
# placeholder CAL instructions locally, thus if we start from the deepest level
# and work our way out we can only resolve a part of the CALs; more precisely,
# we can only resolve the part of CALs that refers to local procedures only.
# Consider the following example:
#
#   procedure A1;
#     procedure B1;
#     begin
#       call A2;  (* <-- point A *)
#     end;
#     procedure B2;
#     begin
#       call B1;  (* <-- point B *)
#     end;
#   begin
#     ! 4
#   end; 
#   procedure A2;
#   begin
#     ! 3
#   end;
#
#   begin
#     call A1;
#     call A2;
#   end.
#
# Procedure A1 would be compiled into:
#
#       JMP 0, Z0
#   A1: ;; (INT instruction ignored since there is no VAR defs in A1)
#       JMP 0, L1
#   B1: ;; (JMP ignored since there is no local procedure)
#       CAL ?, ?  ;; <-- point A
#       OPR 0, 0
#   B2: CAL ?, ?  ;; <-- point B
#       OPR 0, 0
#   L1: LIT 0, 4
#       OPR 0, 14
#       OPR 0, 0
#   A2: ;; (INT instruction ignored since there is no VAR defs in A2)
#       ;; (JMP instruction ignored since there is no local procedure)
#       LIT 0, 3
#       OPR 0, 14
#       OPR 0, 0
#   Z0: CAL ?, ?
#       CAL ?, ?
#
# We must know that when compiling A1 we have no info on the location of A2.
# The compilation of A1 yields two placeholder CALs: one at B1 for function
# A2, one at B2 for function B1. Since B1 is local we are able to get its
# location, but we can't say the same thing about A2.
# From this we can refine the list of things to do when compiling a block:
# 1.  Collect all constant definitions.
# 2.  Allocate variables.
# 3.  Compile all local procedures.
# 4.  Record the locations of local procedures.
# 5.  Resolve placeholder CALs only for the call to the local procedures
#     recorded in step 4. The rest would have to be resolved when compiling
#     for outer layers. The depth is maintained by increasing by one with
#     each ascension of layers.
# 6.  Compile block body.
# This process would still generate a list of placeholder CALs that are not
# resolved; thus the return type of this function still has a seq[(int, int, string)].
# Compiling a proc is mostly the same as compiling a block, the difference
# being that when compiling a proc the name of the proc is added to the
# environment to enable recursion. The name of the proc, when resolving, has
# a depth of 1 (instead of 0 like calling local procedures) since technically
# lives in the parent scope.
proc compileProcOrBlock(x: Block, name: string, currentLoc: int, layerCount: int, env: var Env): (seq[Instr], seq[(int, int, string)]) =
  # echo "compiling ", name, " at loc ", currentLoc, " at layer ", layerCount
  var blockBase = currentLoc
  let constTable = if x.constDef.len <= 0: nil else: x.collectConst
  var res: seq[Instr] = @[]
  var callFillers: seq[(int, int, string)] = @[]
  var procTable: TableRef[string, int] = newTable[string, int]()
  var varTable: TableRef[string, (int, int)] = nil
  if x.varDef.len > 0:
    res.add((INT, 0, x.varDef.len))
    varTable = x.allocVar(layerCount)
    blockBase += 1
  let newEnvFrame = (constTable: constTable,
                     varTable: varTable,
                     procTable: procTable)
  env.add(newEnvFrame)
  if x.procDef.len > 0:
    # NOTE: we can resolve this locally because we can calculate the sizes of
    # local procedures locally. This is a placeholder that we'll resolve later.
    res.add((JMP, 0, 0))
    blockBase += 1
    var procLocationCount = blockBase
    for p in x.procDef:
      let name = p[0]
      let def = p[1]
      procTable[name] = procLocationCount
      let pRes = def.compileProcOrBlock(name, procLocationCount, layerCount+1, env)
      res &= pRes[0]
      callFillers &= pRes[1]
      procLocationCount += pRes[0].len
    # NOTE: since the whole proc starts at currentLoc, one can find the
    # relative location of the CALs by i-currentLoc.
    var newCallFillers: seq[(int, int, string)] = @[]
    for c in callFillers:
      let calLoc = c[0]
      let calName = c[2]
      # NOTE: for the reason stated in the comment above, the calName == name
      # and the else clause have to be like this for the fac_recursive.pl0
      # example to work correctly.
      if calName == name:
        res[calLoc-currentLoc] = (CAL, 1, currentLoc)
      elif procTable.hasKey(calName):
        res[calLoc-currentLoc] = (CAL, c[1], procTable[calName])
      else:
        newCallFillers.add((c[0], c[1]+1, c[2]))
    callFillers = newCallFillers
    # resolving the JMP we setup in the beginning...
    res[blockBase-1-currentLoc] = (JMP, 0, procLocationCount)
    blockBase = procLocationCount

  let bodyRes = x.body.compileStatement(blockBase, layerCount, env)
  discard env.pop()
  res &= bodyRes[0]
  let bodyCallFillers = bodyRes[1]
  for c in bodyCallFillers:
    let calLoc = c[0]
    let calName = c[2]
    if calName == name:
      res[calLoc-currentLoc] = (CAL, 1, currentLoc)
    elif procTable.hasKey(calName):
      res[calLoc-currentLoc] = (CAL, c[1], procTable[calName])
    else:
      callFillers.add((c[0], c[1]+1, c[2]))
  if name.len > 0:
    res.add((OPR, 0, 0))
  return (res, callFillers)

proc compileProgram(x: Program): seq[Instr] =
  var env: Env = @[]
  let res = x.body.compileProcOrBlock("", 0, 0, env)
  assert(res[1].len <= 0)
  return res[0]

# vm.
type
  VM = ref object
    pc: int
    base: int
    stk: int
    stkmem: array[2048,int]
    program: seq[Instr]

proc loadVM(program: seq[Instr]): VM =
  VM(pc: 0,
     base: 1,
     stk: 0,
     program: program)
    
proc runVM(vm: VM): void =
  
  # NOTE: this traces the static link)
  proc traceStaticLink(vm: VM, currentBase: int, layerCount: int): int =
    var subj = currentBase
    var lc = layerCount
    while lc > 0:
      subj = vm.stkmem[subj]
      lc -= 1
    return subj
    
  while vm.pc < vm.program.len:
    let i = vm.program[vm.pc]
    let iType = i[0]
    let iLayer = i[1]
    let iArg = i[2]
    case iType:
      of LIT:
        vm.stk += 1
        vm.stkmem[vm.stk] = iArg
        vm.pc += 1
      of OPR:
        case iArg:
          of 0:  # return
            # prev. stktop
            # static link
            # dynamic link
            # retaddr
            vm.stk = vm.base-1
            vm.pc = vm.stkmem[vm.stk+3]
            vm.base = vm.stkmem[vm.stk+2]
          of 1:
            vm.stkmem[vm.stk] = -vm.stkmem[vm.stk]
            vm.pc += 1
          of 2:
            vm.stk -= 1
            vm.stkmem[vm.stk] += vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 3:
            vm.stk -= 1
            vm.stkmem[vm.stk] -= vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 4:
            vm.stk -= 1
            vm.stkmem[vm.stk] *= vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 5:
            vm.stk -= 1
            vm.stkmem[vm.stk] = vm.stkmem[vm.stk] div vm.stkmem[vm.stk+1]
            vm.pc += 1
          of 6:
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] mod 2 == 1: 1 else: 0
            vm.pc += 1
          of 7:  # input
            stdout.write("? "); stdout.flushFile()
            let z = stdin.readLine().parseInt
            vm.stk += 1
            vm.stkmem[vm.stk] = z
            vm.pc += 1
          of 8:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] == vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 9:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] != vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 10:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] < vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 11:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] <= vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 12:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] > vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 13:
            vm.stk -= 1
            vm.stkmem[vm.stk] = if vm.stkmem[vm.stk] >= vm.stkmem[vm.stk+1]: 1 else: 0
            vm.pc += 1
          of 14:  # print
            echo vm.stkmem[vm.stk]
            vm.stk -= 1
            vm.pc += 1
          of 15:  # halt
            break
          else:
            raise newException(ValueError, &"[VM] Unsupported OPR function: {iArg}")
      of LOD:
        vm.stk += 1
        vm.stkmem[vm.stk] = vm.stkmem[vm.traceStaticLink(vm.base, iLayer) + iArg]
        vm.pc += 1
      of STO:
        vm.stkmem[vm.traceStaticLink(vm.base, iLayer) + iArg] = vm.stkmem[vm.stk]
        vm.stk -= 1
        vm.pc += 1
      of CAL:
        vm.stkmem[vm.stk+1] = vm.traceStaticLink(vm.base, iLayer)
        vm.stkmem[vm.stk+2] = vm.base
        vm.stkmem[vm.stk+3] = vm.pc+1
        vm.base = vm.stk+1
        vm.pc = iArg
        vm.stk = vm.stk+3
      of INT:
        vm.stk += iArg
        vm.pc += 1
      of JMP:
        vm.pc = iArg
      of JPC:
        if vm.stkmem[vm.stk] == 0:
          vm.pc = iArg
          vm.stk -= 1
        else:
          vm.pc += 1

# NOTE THAT in the definition of JPC we jump when the stacktop is *0* but the
# comparison operators leave *1* at the stack top when the conditio holds;
# this is differnt from what we are used to but I believe this has a very
# simple reason. Consider this example:
# 
#   if a > 3 then
#   begin
#     a := 3;
#   end;
#
# If JPC jumps when stacktop is 1 then the compiled code should be:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       JMP 0, L2
#   L1: LIT 0, 3
#       STO (a)
#   L2:
#
# But if JPC jumps when stacktop is 0 then the compiled code should be:
#
#       LOD (a)
#       LIT 0, 3
#       OPR 0, 12
#       JPC 0, L1
#       LIT 0, 3
#       STO (a)
#   L1:
#
# Which is one instruction less; this design desicion would have the same
# effect on compiling WHILE.

when isMainModule:
  if paramCount() < 1:
    echo "Input file needed. Usage: pl0 [input-file]"
    quit(0)
  let fileName = paramStr(1)
  let f = open(fileName, fmRead)
  let source = f.readAll()
  f.close()
  let parseRes = parseProgram(source)
  if parseRes.isSome():
    let compileRes = parseRes.get.compileProgram
    # for k in compileRes: echo k
    loadVM(compileRes).runVM
  
