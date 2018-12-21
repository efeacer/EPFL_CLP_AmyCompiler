package amyc
package analyzer

import utils._
import ast.{Identifier, NominalTreeModule => N, SymbolicTreeModule => S}

// Name analyzer for Amy
// Takes a nominal program (names are plain strings, qualified names are string pairs)
// and returns a symbolic program, where all names have been resolved to unique Identifiers.
// Rejects programs that violate the Amy naming rules.
// Also populates and returns the symbol table.
object NameAnalyzer extends Pipeline[N.Program, (S.Program, SymbolTable)] {
  def run(ctx: Context)(p: N.Program): (S.Program, SymbolTable) = {
    import ctx.reporter._

    // Step 0: Initialize symbol table
    val table = new SymbolTable

    // Step 1: Add modules to table 
    val modNames = p.modules.groupBy(_.name)
    modNames.foreach { case (name, modules) =>
      if (modules.size > 1) {
        fatal(s"Two modules named $name in program", modules.head.position)
      }
    }

    modNames.keys.toList foreach table.addModule


    // Helper method: will transform a nominal type 'tt' to a symbolic type,
    // given that we are within module 'inModule'.
    def transformType(tt: N.TypeTree, inModule: String): S.Type = {
      tt.tpe match {
        case N.IntType => S.IntType
        case N.BooleanType => S.BooleanType
        case N.StringType => S.StringType
        case N.UnitType => S.UnitType
        case N.ClassType(qn@N.QualifiedName(module, name)) =>
          table.getType(module getOrElse inModule, name) match {
            case Some(symbol) =>
              S.ClassType(symbol)
            case None =>
              fatal(s"Could not find type $qn", tt)
          }
      }
    }

    // Step 2: Check name uniqueness of definitions in each module
    for (module <- p.modules) {
      for (mapping <- module.defs.groupBy(_.name)) {
        mapping match {
          case (name, definitions) =>
            if (definitions.size > 1) { //definition is not unique
              fatal("More than one definitions found for " + name + " in " + module.name, definitions.head.position)
            }
          case _ => // default
        }
      }
    }

    // Step 3: Discover types and add them to symbol table
    for (module <- p.modules) {
      for (definition <- module.defs) {
        definition match {
          case N.AbstractClassDef(name) => table.addType(module.name, name)
          case _ => // default
        }
      }
    }

    // Step 4: Discover type constructors, add them to table
    for (module <- p.modules) {
      for (definition <- module.defs) {
        definition match {
          case N.CaseClassDef(name, fields, parent) =>
            table.addConstructor(module.name, name, fields.map(tType => transformType(tType, module.name)), // arguments
              table.getType(module.name, parent).getOrElse(fatal("Type not found: " + module.name)))
          case _ => // default
        }
      }
    }

    // Step 5: Discover functions signatures, add them to table
    for (module <- p.modules) {
      for (definition <- module.defs) {
        definition match {
          case N.FunDef(name, parameters, returnType, _) =>
            table.addFunction(module.name, name,
              parameters.map(parameter => parameter.tt).map(tType => transformType(tType, module.name)), // LOOK AGAIN
              transformType(returnType, module.name))
          case _ => // default
        }
      }
    }

    // Step 6: We now know all definitions in the program.
    //         Reconstruct modules and analyse function bodies/ expressions
    
    // This part is split into three transfrom functions,
    // for definitions, FunDefs, and expressions.
    // Keep in mind that we transform constructs of the NominalTreeModule 'N' to respective constructs of the SymbolicTreeModule 'S'.
    // transformFunDef is given as an example, as well as some code for the other ones

    def transformDef(df: N.ClassOrFunDef, module: String): S.ClassOrFunDef = { df match {
      case N.AbstractClassDef(name) =>
        val ident = table.getType(module, name).get
        S.AbstractClassDef(ident)
      case N.CaseClassDef(name, _, _) =>
        val (ident, signature) = table.getConstructor(module, name).get
        val ConstrSig(argTypes, parent, _) = signature
        S.CaseClassDef(ident, argTypes.map(arg => S.TypeTree(arg)), parent)
      case fd: N.FunDef =>
        transformFunDef(fd, module)
    }}.setPos(df)

    def transformFunDef(fd: N.FunDef, module: String): S.FunDef = {
      val N.FunDef(name, params, retType, body) = fd
      val Some((sym, sig)) = table.getFunction(module, name)

      params.groupBy(_.name).foreach { case (name, ps) =>
        if (ps.size > 1) {
          fatal(s"Two parameters named $name in function ${fd.name}", fd)
        }
      }

      val paramNames = params.map(_.name)

      val newParams = params zip sig.argTypes map { case (pd@N.ParamDef(name, tt), tpe) =>
        val s = Identifier.fresh(name)
        S.ParamDef(s, S.TypeTree(tpe).setPos(tt)).setPos(pd)
      }

      val paramsMap = paramNames.zip(newParams.map(_.name)).toMap

      S.FunDef(
        sym,
        newParams,
        S.TypeTree(sig.retType).setPos(retType),
        transformExpr(body)(module, (paramsMap, Map()))
      ).setPos(fd)
    }

    // This function takes as implicit a pair of two maps:
    // The first is a map from names of parameters to their unique identifiers,
    // the second is similar for local variables.
    // Make sure to update them correctly if needed given the scoping rules of Amy
    def transformExpr(expr: N.Expr)
                     (implicit module: String, names: (Map[String, Identifier], Map[String, Identifier])): S.Expr = {
      val (params, locals) = names
      val res = expr match {
        case N.Match(scrut, cases) =>
          // Returns a transformed pattern along with all bindings
          // from strings to unique identifiers for names bound in the pattern.
          // Also, calls 'fatal' if a new name violates the Amy naming rules.
          def transformPattern(pat: N.Pattern): (S.Pattern, List[(String, Identifier)]) = {
            pat match {
              case N.WildcardPattern() => (S.WildcardPattern().setPos(pat), List())
              case N.IdPattern(name) =>
                val ident = Identifier.fresh(name)
                (S.IdPattern(ident).setPos(pat), List((name, ident)))
              case N.LiteralPattern(lit) =>
                val sLit = lit match {
                  case N.IntLiteral(value) => S.IntLiteral(value).setPos(lit)
                  case N.StringLiteral(value) => S.StringLiteral(value).setPos(lit)
                  case N.BooleanLiteral(value) => S.BooleanLiteral(value).setPos(lit)
                  case N.UnitLiteral() => S.UnitLiteral().setPos(lit)
                }
                (S.LiteralPattern(sLit).setPos(pat), Nil)
              case N.CaseClassPattern(constructor, args) =>
                val owner = constructor.module.getOrElse(module)
                val name = constructor.name
                val sConstructor = table.getConstructor(owner, name)
                val (id, constructorSignature) = sConstructor.getOrElse(fatal("Constructor not found: " + owner + "." + name))
                if (constructorSignature.argTypes.size != args.size) {
                  fatal("Argument number does not match: " + owner + "." + name, pat)
                }
                val transformedArguments = args.map(arg => transformPattern(arg))
                val patArguments = transformedArguments.map(arg => arg._1)
                val patLocals = transformedArguments.flatMap(arg => arg._2)
                if (patLocals.map(_._1).distinct.size < patLocals.size) {
                  fatal("Multiple definitions found in pattern.", pat)
                }
                (S.CaseClassPattern(id, patArguments).setPos(pat), patLocals)
            }
          }

          def transformCase(cse: N.MatchCase) = {
            val N.MatchCase(pat, rhs) = cse
            val (newPat, moreLocals) = transformPattern(pat)
            val newLocals = locals.keySet.intersect(moreLocals.toMap.keySet)
            if (newLocals.nonEmpty) {
              fatal("Pattern identifier " + newLocals.head + " defined more than once.", pat)
            }
            S.MatchCase(newPat, transformExpr(rhs)(module, (params, locals ++ moreLocals.toMap))).setPos(cse)
          }

          S.Match(transformExpr(scrut), cases.map(transformCase))

        // rest of the cases:

        // calls
        case N.Call(qName, args) =>
          val owner = qName.module.getOrElse(module)
          val name = qName.name
          val (sName, constructorSignature) = table.getConstructor(owner, name).getOrElse(table.getFunction(owner,name).
            getOrElse(fatal("Function/Constructor cannot be found: " + owner + "." + name, expr)))
          if (constructorSignature.argTypes.size != args.size) {
            fatal("Argument number does not match: " + owner + "." + name, expr)
          }
          S.Call(sName, args.map(arg => transformExpr(arg)))
        // let
        case N.Let(df, value, body) =>
          val sName = Identifier.fresh(df.name)
          val parameterDefinition = S.ParamDef(sName, S.TypeTree(transformType(df.tt, module)))
          val sValue = transformExpr(value)
          if (locals.contains(df.name)) {
            fatal("Variable is defined multiple times: " + df.name, df.position)
          }
          val sBody = transformExpr(body)(module, (params, locals + (df.name -> sName)))
          S.Let(parameterDefinition, sValue, sBody)
        // sequence
        case N.Sequence(e1, e2) => S.Sequence(transformExpr(e1), transformExpr(e2))
        // if then else
        case N.Ite(condition, thenBlock, elseBlock) => S.Ite(transformExpr(condition), transformExpr(thenBlock), transformExpr(elseBlock))
        // variable
        case N.Variable(name) =>
          S.Variable(locals.getOrElse(name, params.getOrElse(name, fatal("Variable " + name + " not found.", expr))))
        // literals
        case N.IntLiteral(value) => S.IntLiteral(value)
        case N.StringLiteral(value) => S.StringLiteral(value)
        case N.BooleanLiteral(value) => S.BooleanLiteral(value)
        case N.UnitLiteral() => S.UnitLiteral()
        // operators
        case N.Plus(lhs, rhs) => S.Plus(transformExpr(lhs), transformExpr(rhs))
        case N.Minus(lhs, rhs) => S.Minus(transformExpr(lhs), transformExpr(rhs))
        case N.Times(lhs, rhs) => S.Times(transformExpr(lhs), transformExpr(rhs))
        case N.Div(lhs, rhs) => S.Div(transformExpr(lhs), transformExpr(rhs))
        case N.Mod(lhs, rhs) => S.Mod(transformExpr(lhs), transformExpr(rhs))
        case N.LessThan(lhs, rhs) => S.LessThan(transformExpr(lhs), transformExpr(rhs))
        case N.LessEquals(lhs, rhs) => S.LessEquals(transformExpr(lhs), transformExpr(rhs))
        case N.Equals(lhs, rhs) => S.Equals(transformExpr(lhs), transformExpr(rhs))
        case N.And(lhs, rhs) => S.And(transformExpr(lhs), transformExpr(rhs))
        case N.Or(lhs, rhs) => S.Or(transformExpr(lhs), transformExpr(rhs))
        case N.Concat(lhs, rhs) => S.Concat(transformExpr(lhs), transformExpr(rhs))
        case N.Not(e) => S.Not(transformExpr(e))
        case N.Neg(e) => S.Neg(transformExpr(e))
        // error
        case N.Error(msg) => S.Error(transformExpr(msg))
      }
      res.setPos(expr)
    }

    // Putting it all together to construct the final program for step 6.
    val newProgram = S.Program(
      p.modules map { case mod@N.ModuleDef(name, defs, optExpr) =>
        S.ModuleDef(
          table.getModule(name).get,
          defs map (transformDef(_, name)),
          optExpr map (transformExpr(_)(name, (Map(), Map())))
        ).setPos(mod)
      }
    ).setPos(p)

    (newProgram, table)

  }
}
