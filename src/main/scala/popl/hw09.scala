package popl

object hw09 extends js.util.JsApp:
  import js.ast._
  import js._
  import Bop._, Uop._, Typ._, PMode._, Mut._
  /*
   * CSCI-UA.0480-055: Homework 9
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your hw09 object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your solution will _not_ be graded if it does not compile!!
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * '???' as needed to get something that compiles without error.
   *
   */

  /* Type Inference */
  
  // A helper function to check whether a JS type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match
    case TFunction(_, _) => true
    case _ => false
  
  def mut(m: PMode): Mut = m match
    case PName | PConst => MConst
    case PLet | PRef => MLet
  
  def typeInfer(env: Map[String, (Mut, Typ)], e: Expr): Typ =
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1)
    def locerr[T](e1: Expr): T = throw LocTypeError(e1)
    def checkTyp(texp: Typ, e1: Expr): Typ =
      val tgot = typ(e1)
      if texp == tgot then texp else err(tgot, e1)
    
    e match
      case Print(e1) => typ(e1); TUndefined
      case Num(_) => TNumber
      case Bool(_) => TBool
      case Undefined => TUndefined
      case Str(_) => TString
      case Var(x) => env(x)._2
      case Decl(mut, x, e1, e2) => 
        typeInfer(env + (x -> (mut, typ(e1))), e2)
      case UnOp(UMinus, e1) => typ(e1) match
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      case UnOp(Not, e1) =>
        checkTyp(TBool, e1)
      case BinOp(bop, e1, e2) =>
        bop match
          case Plus =>
            typ(e1) match
              case TNumber => checkTyp(TNumber, e2)
              case TString => checkTyp(TString, e2)
              case tgot => err(tgot, e1)
          case Minus | Times | Div => 
            checkTyp(TNumber, e1)
            checkTyp(TNumber, e2)
          case Eq | Ne => typ(e1) match
            case t1 if !hasFunctionTyp(t1) => 
              checkTyp(t1, e2); TBool
            case tgot => err(tgot, e1)
          case Lt | Le | Gt | Ge =>
            typ(e1) match
              case TNumber => checkTyp(TNumber, e2)
              case TString => checkTyp(TString, e2)
              case tgot => err(tgot, e1)
            TBool
          case And | Or =>
            checkTyp(TBool, e1)
            checkTyp(TBool, e2)
          case Seq =>
            typ(e1); typ(e2)
          case Assign =>
            e1 match
              case Var(x) =>
                env(x) match
                  case (MLet, t) => checkTyp(t, e2)
                  case _ => locerr(e1)             
              case _ => locerr(e1)
      case If(e1, e2, e3) =>
        checkTyp(TBool, e1)
        val t2 = typ(e2)
        checkTyp(t2, e3)
      case Function(p, xs, tann, e1) =>
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(xs map (_._2), tret)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        // Bind to env2 an environment that extends env1 with bindings for xs.
        val env2 = xs.foldLeft(env1){
          case (env2, (x, (pm, t))) => env2 + (x -> (mut(pm), t)) 
        }
        // Match on whether the return type is specified.
        tann match
          case None => TFunction(xs map (_._2), typeInfer(env2, e1))
          case Some(tret) => 
            typeInfer(env2, e1) match
              case tbody if tbody == tret => 
                TFunction(xs map (_._2), tret)
              case tbody => err(tbody, e1)
      case Call(e1, es) => typ(e1) match
        case TFunction(txs, tret) if (txs.length == es.length) =>
          txs.lazyZip(es).foreach {
            case ((PConst|PLet|PName, t), e) => checkTyp(t, e)
            case ((PRef, t), e @ Var(x)) => 
              env(x) match
                case (MLet, tgot) => 
                  if (tgot != t) err(tgot, e)
                case (MConst, _) => locerr(e)
            case ((PRef, _), e) => locerr(e)
          }
          tret
        case tgot => err(tgot, e1)
      case Addr(_) | UnOp(Deref, _) => 
        throw IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
  
  /* JakartaScript Interpreter */
  
  def toNum(v: Val): Double = v match
    case Num(n) => n
    case _ => throw StuckError(v)
  
  def toBool(v: Val): Boolean = v match
    case Bool(b) => b
    case _ => throw StuckError(v)
  
  def toStr(v: Val): String = v match
    case Str(s) => s
    case _ => throw StuckError(v)
  
  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Val, v2: Val): Boolean =
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match
      case (Str(s1), Str(s2)) =>
        (bop: @unchecked) match
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
      case _ =>
        val (n1, n2) = (toNum(v1), toNum(v2))
        (bop: @unchecked) match
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
  
  /* 
   * Substitutions e[er/x]
   */
  def subst(e: Expr, x: String, er: Expr): Expr =
    require(closed(er))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def substX(e: Expr): Expr = subst(e, x, er)
    /* Body */
    e match
      case Num(_) | Bool(_) | Undefined | Str(_) | Addr(_) => e
      case Var(y) => if x == y then er else e
      case Print(e1) => Print(substX(e1))
      case UnOp(uop, e1) => UnOp(uop, substX(e1))
      case BinOp(bop, e1, e2) => BinOp(bop, substX(e1), substX(e2))
      case If(b, e1, e2) => If(substX(b), substX(e1), substX(e2))
      case Call(e0, es) =>
        Call(substX(e0), es map substX)
      case Decl(mut, y, ed, eb) => 
        Decl(mut, y, substX(ed), if x == y then eb else substX(eb))
      case Function(p, ys, tann, eb) => 
        if p.contains(x) || (ys exists (_._1 == x)) then e 
        else Function(p, ys, tann, substX(eb))

  
  /*
   * Big-step interpreter.
   */
  def eval(m: Mem, e: Expr): (Mem, Val) =
    require(closed(e), "eval called on non-closed expression:\n" + e.prettyJS)
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): (Mem, Val) = eval(m, e)
    def eToNum(m: Mem, e: Expr): (Mem, Double) =
      val (mp, v) = eval(m, e)
      (mp, toNum(v))
    def eToBool(m: Mem, e: Expr): (Mem, Boolean) =
      val (mp, v) = eval(m, e)
      (mp, toBool(v))
    e match
      // EvalVal
      case v: Val => (m, v)
      
      // EvalPrint
      case Print(e) => 
        val (mp, v) = eToVal(e)
        println(v.prettyVal) 
        (mp, Undefined)
      
      // EvalUMinus
      case UnOp(UMinus, e1) =>
        val (mp, n) = eToNum(m, e1)
        (mp, Num(-n))
      
      // EvalNot
      case UnOp(Not, e1) =>
        val (mp, b) = eToBool(m, e1)
        (mp, Bool(! b))
    
      // EvalDerefVar
      case UnOp(Deref, a: Addr) =>
        (m, m(a))
        
      // EvalPlusNum, EvalPlusStr
      case BinOp(Plus, e1, e2) => 
        val (m1, v1) = eval(m, e1) 
        val (m2, v2) = eval(m1, e2)
        val v = (v1, v2) match
          case (Str(s1), v2) => Str(s1 + toStr(v2))
          case (v1, Str(s2)) => Str(toStr(v1) + s2)
          case (v1, v2) => Num(toNum(v1) + toNum(v2))
        (m2, v)
      
      // EvalArith
      case BinOp(bop@(Minus|Times|Div), e1, e2) => 
        val (m1, n1) = eToNum(m, e1) 
        val (m2, n2) = eToNum(m1, e2)
        
        val n = (bop: @unchecked) match
          case Minus => n1 - n2
          case Times => n1 * n2
          case Div => n1 / n2
        (m2, Num(n))
      
      // EvalAndTrue, EvalAndFalse
      case BinOp(And, e1, e2) => 
        val (m1, b) = eToBool(m, e1)
        if b then eval(m1, e2) // EvalAndTrue
        else (m1, Bool(b)) // EvalAndFalse
      
      // EvalOrTrue, EvalOrFalse
      case BinOp(Or, e1, e2) =>
        val (m1, b) = eToBool(m, e1)
        if b then (m1, Bool(b)) // EvalOrTrue
        else eval(m1, e2) // EvalOrFalse
      
      // EvalSeq
      case BinOp(Seq, e1, e2) => 
        val (m1, _) = eval(m, e1)
        eval(m1, e2)
      
      // EvalAssignVar
      case BinOp(Assign, UnOp(Deref, a: Addr), e2) =>
        val (mp, v2) = eval(m, e2)
        (mp + (a -> v2), v2)
        
      // EvalEqual, EvalInequalNum, EvalInequalStr
      case BinOp(bop@(Eq|Ne|Lt|Gt|Le|Ge), e1, e2) =>
        val (m1, v1) = eval(m, e1)
        val (m2, v2) = eval(m1, e2)
        val v = (bop: @unchecked) match
          case Eq => Bool(v1 == v2)
          case Ne => Bool(v1 != v2)
          case Le|Ge|Lt|Gt => Bool(inequalityVal(bop, v1, v2))
        (m2, v)
        
      // EvalIfThen, EvalIfElse
      case If(e1, e2, e3) => 
        val (m1, b) = eToBool(m, e1)
        if b then eval(m1, e2) // EvalIfThen 
        else eval(m1, e3) // EvalIfElse
      
      // EvalConstDecl
      case Decl(MConst, x, ed, eb) => 
        val (md, vd) = eval(m, ed)
        eval(md, subst(eb, x, vd))
      
      // EvalVarDecl
      case Decl(MLet, x, ed, eb) =>
        val (md, vd) = eval(m, ed)
        val (mp, a) = md.alloc(vd)
        eval(mp, subst(eb, x, UnOp(Deref, a)))
        
      // EvalCall*
      case Call(e0, es) =>
        val (m0, v0) = eval(m, e0)
        v0 match
          // EvalCallRec
          case v0@Function(Some(x0), _, _, _) => 
            val v0p = subst(v0.copy(p=None), x0, v0)
            eval(m0, Call(v0p, es))
            
          // EvalCallConst, EvalCallName, EvalCallRef, EvalCallVar
          case v0@Function(None, (x1, (mode, _)) :: xs, _, eb) =>
            (mode, es) match
              // EvalCallConst
              case (PConst, e1 :: es) =>
                val (m1, v1) = eval(m0, e1)
                val v0p = v0.copy(xs=xs, e=subst(eb, x1, v1))
                eval(m1, Call(v0p, es))
              
              // EvalCallName, EvalCallRef
              case (PName|PRef, e1 :: es) =>
                val v0p = v0.copy(xs=xs, e=subst(eb, x1, e1))
                eval(m0, Call(v0p, es))
                
              // EvalCallVar
              case (PLet, e1 :: es) =>
                val (m1, v1) = eval(m0, e1)
                val (mp, a) = m1.alloc(v1)
                val v0p = v0.copy(xs=xs, e=subst(eb, x1, UnOp(Deref, a)))
                eval(mp, Call(v0p, es))
              case _ => throw StuckError(e)
          
          // EvalCall
          case Function(None, Nil, _, eb) =>
            eval(m0, eb)
            
          case _ => throw StuckError(e)
        
      case Var(_) | UnOp(Deref, _) | BinOp(_, _, _) => 
        throw StuckError(e) // this should never happen
   
  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def evaluate(e: Expr): Val = eval(Mem.empty, e)._2
  
  def evaluate(s: String): Val = eval(Mem.empty, parse.fromString(s))._2
    
  def inferType(s: String): Typ = typeInfer(Map.empty, parse.fromString(s))
     
  
  /* Interface to run your interpreter from the command line.  You can ignore the code below. */ 
  
  def processFile(file: java.io.File): Unit =
    if debug then
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    
    val expr = handle(fail()) {
      parse.fromFile(file)
    }
      
    if debug then
      println("Parsed expression:")
      println(expr)
    
    handle(fail()) {
      val t = typeInfer(Map.empty, expr)
    }
    
    handle(()) {
      val (_, v) = eval(Mem.empty, expr)
      println(v.prettyVal)
    }
    
end hw09
