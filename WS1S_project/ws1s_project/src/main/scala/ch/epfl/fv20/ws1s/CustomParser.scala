package ch.epfl.fv20.ws1s

import ch.epfl.fv20.ws1s.Language.{Not, _}
import ch.epfl.fv20.ws1s.Lexer.Tokens

import ch.epfl.fv20.ws1s.Lexer.Tokens.{Successor1, _}

import scala.collection.mutable
import scala.io.StdIn
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.{NoPosition, Position, Reader}

/*
This file is the exact same as the other one with "Value" renamed "Variable" and still compile.
It should parse the user input into a tree as described in Language, as the process of implementing first and second order values is much too complex to be
directly implemented from the input text into the Kernel. Technically, this is the parser and the file "Translator" really is the interpreter.
 */
object CustomParser {
  val T = ch.epfl.fv20.ws1s.Lexer.Tokens
  val L = ch.epfl.fv20.ws1s.Language


  object Parser extends Parsers {

    case class Macro(name: String, args: List[String], formula: BooleanFormula)

    private val macros: mutable.Map[String, Macro] = new mutable.HashMap[String, Macro]()

    override type Elem = T.Token

    def identifier: Parser[String] = {
      accept("identifier", { case Identifier(name) => name })
    }

    def macrodef: Parser[Macro] = {
      (Def() ~ identifier.filter(_.startsWith("_")) ~ LPar() ~ repsep(identifier.filter(n => !n.startsWith("_")), accept(Comma())) ~ RPar() ~ Colon() ~ operation) ^^ {
        case _ ~ id ~ _ ~ args ~ _ ~ _ ~ formula => Macro(id, args, formula)
      }
    }

    def variable1: Parser[Variable1] = identifier.filter(name => name(0) != '_' && name(0).isLower) ^^ { name => Variable1(name) }
    def variable2: Parser[Variable2] = identifier.filter(name => name(0) != '_' && !name(0).isLower) ^^ { name => Variable2(name) }
    def macroUse: Parser[BooleanFormula] = (identifier.filter(_.startsWith("_")) ~ (LPar() ~> repsep(value1 | value2, accept(Comma())) <~ RPar())).flatMap {
      case identifier ~ args =>
        if (!macros.contains(identifier)) return err("Invalid macro " + identifier)

        val macr = macros(identifier)
        if (macr.args.length != args.length) return err("Invalid number of arguments for macro " + identifier + "(" + macr.args.mkString(", ") + ")")

        val (formula, error) = macr.args.zip(args).foldLeft((Option(macr.formula), Option.empty[String]))((a, b) => (a, b) match {
          case ((Some(formula), None), (argName, argValue: Value1)) if argName(0).isLower =>
            (Some(formula.substitute(Variable1(argName), argValue)), None)
          case ((Some(formula), None), (argName, argValue: Value2)) if argName(0).isUpper =>
            (Some(formula.substitute(Variable2(argName), argValue)), None)
          case ((_, None), (argName, argValue)) =>
            (None, Some("Invalid argument type for argument " + argName + ". Expected: " + (if (argName(0).isUpper) "2nd order value" else "1st order value") + ". Got:" + argValue.getClass))
          case ((_, err), _) => (None, err)
        })

        if (error.nonEmpty) err(error.get)
        else if (formula.nonEmpty) success(formula.get)
        else err("Empty error when applying macro (should never happen)")
    }

    def intlit1 = accept("int litteral", { case IntLiteral(num) => Constant1(num) })

    def value1: Parser[Value1] = {
      def successor: Parser[Value1] = Next1() ~> value1 ^^ {
        v1 => Language.Successor(v1)
      }

      def paren: Parser[Value1] = LPar() ~> value1 <~ RPar()

      def plus = chainl1(intlit1 | variable1 | successor | paren, intlit1, Plus() ^^^ {
        (l: Value1, r: Constant1) => Plus_n(l, r)
      })

      plus
    }

    def value2: Parser[Value2] = {
      def constant = Lift() ~> intlit1 ^^ { l => ConstantInteger2(l.n) }
      def constantPredicate = LBrack() ~> repsep(value1, accept(Comma())) <~ RBrack() ^^ { set => ConstantPredicate(set.toSet) }
      def paren = LSq() ~> value2 <~ RSq()

      def operations: Parser[(Value2, Value2) => Value2] = ((Tokens.Union() | Tokens.Inter() | Tokens.Plus())) ^^ {
        case Tokens.Union() => Language.Union
        case Tokens.Inter() => Intersection
        case Tokens.Plus() => Sum
      }

      def op = chainl1(constant | constantPredicate | variable2 | paren, operations)

      def opMul = chainl1(op, constant, Times() ^^^ { (l: Value2, r: ConstantInteger2) => Product(l, r) })

      opMul
    }

    def operation: Parser[BooleanFormula] = {
      def constant: Parser[BooleanFormula] = (True() ^^^ L.T) | (False() ^^^ L.F)

      def par = (LPar() ~! operation ~! RPar() ^^ { case _ ~ f ~ _ => f })

      def not = T.Not() ~! operation ^^ { case _ ~ e => Not(e) }

      def varOps = {

        def succ =
          Successor1() ~> LPar() ~> value1 ~ (Comma() ~> value1 <~ RPar()) ^^ { case v1 ~ v2 => Succ1(v1, v2) } |
            Successor2() ~> LPar() ~> value2 ~ (Comma() ~> value2 <~ RPar()) ^^ { case v1 ~ v2 => Succ2(v1, v2) }

        def op1 = value1 ~ ((Equals() ~ value1) | (T.In() ~ value2)) ^^ {
          case v1 ~ (Equals() ~ (v2: Value1)) => Equal1(v1, v2)
          case v1 ~ (Tokens.In() ~ (v2: Value2)) => Language.In(v1, v2)
        }

        def op2 = value2 ~ (Equals() | T.In()) ~ value2 ^^ {
          case v1 ~ Equals() ~ v2 => Equal2(v1, v2)
          case v1 ~ T.In() ~ v2 => Language.Subset(v1, v2)
        }

        op1 | op2 | succ
      }


      def quantifiers = ((T.Forall() | T.Exists()) ~ (variable1 | variable2) ~ Colon() ~ operation) ^^ {
        case Tokens.Forall() ~ id ~ _ ~ op => Language.Forall(id, op)
        case Tokens.Exists() ~ id ~ _ ~ op => Language.Exists(id, op)
      }

      def formula: Parser[BooleanFormula] = par | not | varOps | quantifiers | constant

      def combinations: Parser[BooleanFormula] = chainl1(formula, combinations, (T.And() | T.Or() | T.Implies()) ^^ {
        case T.And() => (l: BooleanFormula, r: BooleanFormula) => L.And(l, r)
        case T.Or() => (l: BooleanFormula, r: BooleanFormula) => L.Or(l, r)
        case T.Implies() => (l: BooleanFormula, r: BooleanFormula) => L.Or(L.Not(l), r)
      })

      combinations
    }

    class TokenReader(tokens: Seq[Token]) extends Reader[Token] {
      override def first: Token = tokens.head

      override def rest: Reader[Token] = new TokenReader(tokens.tail)

      override def pos: Position = if (atEnd) NoPosition else first.pos

      override def atEnd: Boolean = tokens.isEmpty
    }

    def apply(tokens: Seq[Token]): Either[NoSuccess, Either[BooleanFormula, Macro]] = {
      phrase((operation | macrodef) ^^ {
        case m: Macro => Right(m)
        case f: BooleanFormula => Left(f)
      })(new TokenReader(tokens)) match {
        case Success(result: Either[BooleanFormula, Macro], next) =>
          if (result.isRight) {
            val macr = result.right.get
            macros.put(macr.name, macr)
          }

          Right(result)
        case ns: NoSuccess => Left(ns)
      }
    }
  }



  //objective is to ask user for input formula and parse it
}
