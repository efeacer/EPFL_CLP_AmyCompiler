package amyc
package codegen

import analyzer._
import ast.Identifier
import ast.SymbolicTreeModule.{Call => AmyCall, Div => AmyDiv, And => AmyAnd, Or => AmyOr, _}
import utils.{Context, Pipeline}
import wasm._
import Instructions._
import Utils._

// Generates WebAssembly code for an Amy program
object CodeGen extends Pipeline[(Program, SymbolTable), Module] {
  def run(ctx: Context)(v: (Program, SymbolTable)): Module = {
    val (program, table) = v

    // Generate code for an Amy module
    def cgModule(moduleDef: ModuleDef): List[Function] = {
      val ModuleDef(name, defs, optExpr) = moduleDef
      // Generate code for all functions
      defs.collect { case fd: FunDef if !builtInFunctions(fullName(name, fd.name)) =>
        cgFunction(fd, name, false)
      } ++
      // Generate code for the "main" function, which contains the module expression
      optExpr.toList.map { expr =>
        val mainFd = FunDef(Identifier.fresh("main"), Nil, TypeTree(IntType), expr)
        cgFunction(mainFd, name, true)
      }
    }

    // Generate code for a function in module 'owner'
    def cgFunction(fd: FunDef, owner: Identifier, isMain: Boolean): Function = {
      // Note: We create the wasm function name from a combination of
      // module and function name, since we put everything in the same wasm module.
      val name = fullName(owner, fd.name)
      Function(name, fd.params.size, isMain){ lh =>
        val locals = fd.paramNames.zipWithIndex.toMap
        val body = cgExpr(fd.body)(locals, lh)
        if (isMain) {
          body <:> Drop // Main functions do not return a value,
                        // so we need to drop the value generated by their body
        } else {
          body
        }
      }
    }

    // Generate code for an expression expr.
    // Additional arguments are a mapping from identifiers (parameters and variables) to
    // their index in the wasm local variables, and a LocalsHandler which will generate
    // fresh local slots as required.
    def cgExpr(expr: Expr)(implicit locals: Map[Identifier, Int], lh: LocalsHandler): Code = {
      expr match {
        // variable definition
        case Let(df, value, body) =>
          val address = lh.getFreshLocal()
          cgExpr(value) <:> SetLocal(address) <:> cgExpr(body)(locals + (df.name -> address), lh)
        // variable
        case Variable(name) => GetLocal(locals(name))
        // literals
        case IntLiteral(lit) => Const(lit)
        case StringLiteral(lit) => mkString(lit)
        case BooleanLiteral(lit) => if (lit) Const(1) else Const(0)
        case UnitLiteral() => Const(0)
        // unary operators
        case Neg(expr1) => Const(0) <:> cgExpr(expr1) <:> Sub
        case Not(expr1) => cgExpr(expr1) <:> Eqz
        // binary operators
        case Plus(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Add
        case Minus(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Sub
        case Times(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Mul
        case AmyDiv(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Div
        case Mod(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Rem
        case Equals(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Eq
        case LessEquals(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Le_s
        case LessThan(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Lt_s
        case AmyAnd(lhs, rhs) => cgExpr(lhs) <:> If_i32 <:> cgExpr(rhs) <:> Else <:> Const(0) <:> End
        case AmyOr(lhs, rhs) => cgExpr(lhs) <:> If_i32 <:> Const(1) <:> Else <:> cgExpr(rhs) <:> End
        case Concat(lhs, rhs) => cgExpr(lhs) <:> cgExpr(rhs) <:> Call(concatImpl.name)
        // sequence of expressions
        case Sequence(expr1, expr2) => cgExpr(expr1) <:> Drop <:> cgExpr(expr2)
        // if then else
        case Ite(condition, thenBlock, elseBlock) =>
          cgExpr(condition) <:> If_i32 <:> cgExpr(thenBlock) <:> Else <:> cgExpr(elseBlock) <:> End
        // match case
        case Match(scrut, cases) =>
          val scrutCodeIndex = lh.getFreshLocal()
          val scrutCode: Code = cgExpr(scrut) <:> SetLocal(scrutCodeIndex)
          def matchAndBind(resultCode: Code, pattern: Pattern): (Code, Map[Identifier, Int]) = {
            pattern match {
              case WildcardPattern() => (resultCode <:> Drop <:> Const(1), locals)
              case LiteralPattern(lit) => (resultCode <:> cgExpr(lit) <:> Eq, locals)
              case IdPattern(name) =>
                val bind = lh.getFreshLocal()
                (resultCode <:> SetLocal(bind) <:> Const(1), locals + (name -> bind))
              case CaseClassPattern(constr, args) =>
                val constrIndex = lh.getFreshLocal()
                val index = table.getConstructor(constr).get.index
                val argsAndNewLocalsCodes = args.zipWithIndex.map(pair =>
                  matchAndBind(GetLocal(constrIndex) <:> Utils.adtField(pair._2) <:> Load, pair._1))
                val argCode: Code = {
                  if (args.isEmpty) Const(1)
                  else if (args.lengthCompare(1) == 0) argsAndNewLocalsCodes.map(_._1)
                  else argsAndNewLocalsCodes.map(_._1) <:> args.tail.map(arg => And)
                }
                val caseClassCode: Code =
                  resultCode <:> SetLocal(constrIndex) <:> GetLocal(constrIndex) <:> Load <:>
                    Const(index) <:> Eq <:> If_i32 <:> argCode <:> Else <:> Const(0) <:> End
                val newLocals = locals ++ argsAndNewLocalsCodes.map(_._2).foldLeft(Map[Identifier,
                    Int]())((m1: Map[Identifier, Int], m2: Map[Identifier, Int]) => m1 ++ m2)
                (caseClassCode, newLocals)
            }
          }
          val caseCodeMapping: List[(MatchCase, (Code, Map[Identifier, Int]))] = cases.map(cse =>
            (cse, matchAndBind(GetLocal(scrutCodeIndex), cse.pat)))
          val caseCodes = caseCodeMapping.map(pair => pair._2._1 <:> If_i32 <:> cgExpr(pair._1.expr)(pair._2._2, lh)
            <:> Else)
          (scrutCode <:> caseCodes <:> mkString("Error in match: ") <:> Call("Std_printString")
            <:> Unreachable <:> cases.map(cse => End))
        // constructor or function call
        case AmyCall(qname, args) =>
          table.getConstructor(qname) match {
            case Some(constrSig) => // constructor call
              val memAddress = lh.getFreshLocal()
              val argCodes: List[Code] = (args.map(arg => cgExpr(arg)) zip (1 to args.size)).map(argCode =>
                GetLocal(memAddress) <:> Const(4 * argCode._2) <:> Add <:> argCode._1 <:> Store)
              GetGlobal(Utils.memoryBoundary) <:> SetLocal(memAddress) <:>
                GetGlobal(Utils.memoryBoundary) <:> Const(4 * (args.size + 1)) <:> Add <:>
                SetGlobal(Utils.memoryBoundary) <:> GetLocal(memAddress) <:> Const(constrSig.index) <:>
                Store <:> argCodes <:> GetLocal(memAddress)
            case None => // function call
              args.map(arg => cgExpr(arg)) <:> Call(Utils.fullName(table.getFunction(qname).get.owner, qname))
          }
        // error
        case Error(msg) =>
          cgExpr(StringLiteral("Error: ")) <:> cgExpr(msg) <:> Call(concatImpl.name) <:> Call("Std_printString") <:>
            Instructions.Unreachable
      }
    }

    Module(
      program.modules.last.name.name,
      defaultImports,
      globalsNo,
      wasmFunctions ++ (program.modules flatMap cgModule)
    )

  }
}
