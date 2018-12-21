package amyc
package parsing

import grammarcomp.parsing._
import utils.Positioned
import ast.NominalTreeModule._
import Tokens._
import amyc.ast.NominalTreeModule

// Implements the translation from parse trees to ASTs for the LL1 grammar,
// that is, this should correspond to Parser.amyGrammarLL1.
// We extend the plain ASTConstructor as some things will be the same -- you should
// override whatever has changed. You can look into ASTConstructor as an example.
class ASTConstructorLL1 extends ASTConstructor {

  override def constructQname(pTree: NodeOrLeaf[Token]): (QualifiedName, Positioned) = {
    pTree match {
      case Node('QName ::= _, List(id, qNameFix)) =>
        val qName = constructQNameFix(qNameFix) // possible DOT() ~ 'Id continuation
        val (name, pos) = constructName(id)
        if (qName == null) (QualifiedName(None, name), pos) else (QualifiedName(Some(name), qName), pos)
    }
  }

  def constructQNameFix(pTree: NodeOrLeaf[Token]): String = { // helper for constructQname
    pTree match {
      case Node('QNameFix ::= _, List(_, id)) =>
        val (name, _) = constructName(id) // DOT() ~ 'Id case
        name
      case _ => null // epsilon() case
    }
  }

  override def constructExpr(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr ::= _, List(Leaf(valToken), param, _, expr2, _, expr)) =>
        Let(constructParam(param), constructExpr2(expr2), constructExpr(expr)).setPos(valToken)
      case Node('Expr ::= _, List(expr2, exprFix)) =>
        val firstExpr = constructExpr2(expr2)
        val secondExpr = constructExprFix(exprFix) // possible continuation
        if (secondExpr == null) firstExpr else Sequence(firstExpr, secondExpr).setPos(firstExpr) // sequence follows or not
    }
  }

  def constructExprFix(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('ExprFix ::= _, List(_, expr)) => constructExpr(expr) // SEMICOLON() ~ 'Expr case
      case _ => null // epsilon() case
    }
  }

  def constructExpr2(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr2 ::= _, List(expr3, expr2Fix)) =>
        val toMatch = constructExpr3(expr3)
        val cases = constructExpr2Fix(expr2Fix) // possible cases to match
        if (cases == null) toMatch else Match(toMatch, constructCases(cases)).setPos(toMatch) // cases follow or not
    }
  }

  def constructExpr2Fix(ptree: NodeOrLeaf[Token]): NodeOrLeaf[Token] = {
    ptree match {
      case Node('Expr2Fix ::= _, List(_, _, cases, _)) => cases
      case _ => null // epsilon() case
    }
  }

  def constructExpr3(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr3 ::= _, List(expr4, expr3Fix)) => // 'Expr4 ~ 'ExprSeq3
        constructOpExpr(constructExpr4(expr4), expr3Fix, constructExpr4) // left associativity
    }
  }

  def constructExpr4(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr4 ::= _, List(expr5, expr4Fix)) => // 'Expr5 ~ 'ExprSeq4
        constructOpExpr(constructExpr5(expr5), expr4Fix, constructExpr5) // left associativity
    }
  }

  def constructExpr5(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr5 ::= _, List(expr6, expr5Fix)) => // 'Expr6 ~ 'ExprSeq5
        constructOpExpr(constructExpr6(expr6), expr5Fix, constructExpr6) // left associativity
    }
  }

  def constructExpr6(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr6 ::= _, List(expr7, expr6Fix)) => // 'Expr7 ~ 'ExprSeq6
        constructOpExpr(constructExpr7(expr7), expr6Fix, constructExpr7) // left associativity
    }
  }

  def constructExpr7(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr7 ::= _, List(expr8, expr7Fix)) => // 'Expr8 ~ 'ExprSeq7
        constructOpExpr(constructExpr8(expr8), expr7Fix, constructExpr8) // left associativity
    }
  }

  def constructExpr8(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr8 ::= _, List(expr9, expr8Fix)) => // 'Expr9 ~ 'ExprSeq8
        constructOpExpr(constructExpr9(expr9), expr8Fix, constructExpr9) // left associativity
    }
  }

  def constructExpr9(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr9 ::= List(MINUS(), _), List(Leaf(minusToken), expr10)) => Neg(constructExpr10(expr10)).setPos(minusToken)
      case Node('Expr9 ::= List(BANG(), _), List(Leaf(bangToken), expr10)) => Not(constructExpr10(expr10)).setPos(bangToken)
      case Node('Expr9 ::= _, List(expr10)) => constructExpr10(expr10) // without any unary operator
    }
  }

  def constructExpr10(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr10 ::= List('Id, _), List(id, expr10Helper2)) =>
        val (qName, args) = constructExpr10Helper2(expr10Helper2) // 'Id ~ 'Expr10Helper2 case
        val (name, pos) = constructName(id)
        if (args == null) Variable(name).setPos(pos) // no arguments to the call
        else {
          if(qName == null || qName.isEmpty) {
            val qualifiedName = QualifiedName(None, name)
            Call(qualifiedName, args).setPos(pos)
          } else {
            val qualifiedName = QualifiedName(Some(name), qName.get)
            Call(qualifiedName, args).setPos(pos)
          }
        }
      case Node('Expr10 ::= List('ExprLiteral), List(currentLiteral)) => constructExprLiteral(currentLiteral) // 'ExprLiteral case
      case Node('Expr10 ::= List(LPAREN(), _), List(Leaf(leftParenToken@LPAREN()), expr10Helper1)) =>
        val expr = constructExpr10Helper1(expr10Helper1) // LPAREN() ~ 'Expr10Helper1 case
        if (expr == null) UnitLiteral().setPos(leftParenToken) else expr.setPos(leftParenToken) // Paranthesis contain expr or not
      case Node('Expr10 ::= (ERROR() :: _), List(Leaf(errPos), _, errMsg, _)) => Error(constructExpr(errMsg)).setPos(errPos) // error case
      case Node('Expr10 ::= (IF() :: _), List(Leaf(iTEToken), _, ifCondition, _, _, ifBlock, _, _, _, elseBlock, _)) =>
        Ite(constructExpr(ifCondition), constructExpr(ifBlock), constructExpr(elseBlock)).setPos(iTEToken) // If then else case
    }
  }

  def constructExprLiteral(ptree: NodeOrLeaf[Token]): Literal[_] = {
    ptree match { // all literals in an expr without paranthesis
      case Node('ExprLiteral ::= List(INTLITSENT), List(Leaf(intToken@INTLIT(i)))) => IntLiteral(i).setPos(intToken)
      case Node('ExprLiteral ::= List(STRINGLITSENT), List(Leaf(stringToken@STRINGLIT(s)))) => StringLiteral(s).setPos(stringToken)
      case Node('ExprLiteral ::= _, List(Leaf(trueToken@TRUE()))) => BooleanLiteral(true).setPos(trueToken)
      case Node('ExprLiteral ::= _, List(Leaf(falseToken@FALSE()))) => BooleanLiteral(false).setPos(falseToken)
    }
  }

  def constructExpr10Helper1(ptree: NodeOrLeaf[Token]): Expr = {
    ptree match {
      case Node('Expr10Helper1 ::= List(RPAREN()), List(_)) => null // no expr inside paranthesis
      case Node('Expr10Helper1 ::= _, List(expr, _)) => constructExpr(expr) // expr is present
    }
  }

  def constructExpr10Helper2(ptree: NodeOrLeaf[Token]): (Option[String], List[Expr]) = {
    ptree match {
      case Node('Expr10Helper2 ::= _, List(qNameFix, _, arguments, _)) =>
        val qName = constructQNameFix(qNameFix)
        val args = constructList(arguments, constructExpr, hasComma = true)
        if (qName == null) (None, args) else (Some(qName), args) // arguments are present or not
      case _ => (null, null) // epsilon() case
    }
  }

  def constructCases(ptree: NodeOrLeaf[Token]): List[MatchCase] = {
    ptree match {
      case Node('Cases ::= _, List(firstCase, casesFix)) => constructCase(firstCase) :: constructCasesFix(casesFix) // all cases
    }
  }

  def constructCasesFix(ptree: NodeOrLeaf[Token]): List[MatchCase] = {
    ptree match {
      case Node('CasesFix ::= ('Cases :: Nil), List(cases)) => constructCases(cases) // cases continue
      case Node('CasesFix ::= _, _) => Nil // epsilon() case
    }
  }

  override def constructPattern(pTree: NodeOrLeaf[Token]): Pattern = {
    pTree match {
      case Node('Pattern ::= List(UNDERSCORE()), List(Leaf(underscoreToken))) =>
        WildcardPattern().setPos(underscoreToken) // wildcard pattern
      case Node('Pattern ::= List('Literal), List(currentLiteral)) =>
        val literal = constructLiteral(currentLiteral)
        LiteralPattern(literal).setPos(literal)
      case Node('Pattern ::= List('Id), List(id)) =>
        val (name, pos) = constructName(id)
        IdPattern(name).setPos(pos)
      case Node('Pattern ::= _, List(id, patternFix)) =>
        val (currentQName, patterns) = constructPatternFix(patternFix) // possible list of patterns
        val (name, pos) = constructName(id)
        if (currentQName == null && patterns == null) {
          IdPattern(name).setPos(pos)
        } else if(currentQName == null) {
          val qName = QualifiedName(None, name)
          CaseClassPattern(qName, patterns).setPos(pos)
        } else {
          val qName = QualifiedName(Some(name), currentQName)
          CaseClassPattern(qName, patterns).setPos(pos)
        }
    }
  }

  def constructPatternFix(pTree: NodeOrLeaf[Token]): (String, List[Pattern]) = {
    pTree match {
      case Node('PatternFix ::= _, List(qNameFix, _, currentPatterns, _)) =>
        val qName = constructQNameFix(qNameFix)
        val patterns = constructList(currentPatterns, constructPattern, hasComma = true)
        if (qName == null)  (null, patterns) else (qName, patterns)
      case _ => (null, null) // epsilon() case
    }
  }

  override def constructOp(ptree: NodeOrLeaf[Token]): (Expr, Expr) => Expr = {
    ptree match {
      case Leaf(token) => tokenToExpr(token)
      case Node(_, List(Leaf(token))) => tokenToExpr(token)
    }
  }

  // Important helper method:
  // Because LL1 grammar is not helpful in implementing left associativity,
  // we give you this method to reconstruct it.
  // This method takes the left operand of an operator (leftopd)
  // as well as the tree that corresponds to the operator plus the right operand (ptree)
  // It parses the right hand side and then reconstruct the operator expression
  // with correct associativity.
  // If ptree is empty, it means we have no more operators and the leftopd is returned.
  // Note: You may have to override constructOp also, depending on your implementation
  def constructOpExpr(leftopd: Expr, ptree: NodeOrLeaf[Token], constructExpr: NodeOrLeaf[Token] => Expr): Expr = { // changed
    ptree match {
      case Node(_, List()) => //epsilon rule of the nonterminals
        leftopd
      case Node(sym ::= _, List(op, rightNode))
        if Set('Expr3Fix, 'Expr4Fix, 'Expr5Fix, 'Expr6Fix, 'Expr7Fix, 'Expr8Fix) contains sym => // changed
        rightNode match {
          case Node(_, List(nextOpd, suf)) => // 'Expr? ::= Expr? ~ 'OpExpr,
            val nextAtom = constructExpr(nextOpd)
            constructOpExpr(constructOp(op)(leftopd, nextAtom).setPos(leftopd), suf, constructExpr) // captures left associativity
        }
    }
  }

}

