package ch.epfl.fv20.ws1s


import scala.util.parsing.combinator.RegexParsers
import scala.util.parsing.input.Positional

object Lexer extends RegexParsers {

  import Tokens._

  // May want to override whiteSpace
  def id: Parser[Identifier] = positioned {
    "[a-zA-Z_][a-zA-Z0-9_]*".r ^^ { str => Identifier(str) }
  }

  def intLit: Parser[IntLiteral] = positioned {
    "-?[0-9]+".r ^^ { s => IntLiteral(s.toInt) }
  }

  def booleans: Parser[Token] = positioned {
    "True" ^^^ True() |
    "False" ^^^ False()
  }

  def boolOps: Parser[Token] = positioned {
    ("||" | "\\/") ^^^ Or() |
      ("&&" | "/\\") ^^^ And() |
      ("->" | "=>") ^^^ Implies() |
      ("!" | "~") ^^^ Not()
  }

  def equals = positioned {
    ("==") ^^^ Equals()
  }

  def quantifiers = positioned {
    ("\\exists" | "\\E") ^^^ Exists() |
      ("\\forall") ^^^ Forall()
  }

  def valOps = positioned {
    ("\\succ" ) ^^^ Successor1() |
    ("++") ^^^ Next1() |
      ("\\union" | "\\U") ^^^ Union() |
      ("\\inter" | "\\I") ^^^ Inter() |
      ("\\SUCC") ^^^ Successor2() |
      "+" ^^^ Plus() |
      "*" ^^^ Times() |
      ("\\subsetof" | "\\in") ^^^ In()
  }

  def symbols = positioned {
    "(" ^^^ LPar() |
      ")" ^^^ RPar() |
      "[" ^^^ LSq() |
      "]" ^^^ RSq() |
      "{" ^^^ LBrack() |
      "}" ^^^ RBrack() |
      ";" ^^^ Semicolon() |
      ":" ^^^ Colon() |
      "," ^^^ Comma()
  }

  def kw = positioned {
    "def" ^^^ Def() |
      "lift" ^^^ Lift()
  }

  def tokens: Parser[List[Token]] = {
    phrase(
      rep1(kw | id | intLit | boolOps | equals | quantifiers | valOps | symbols)
    )
  }

  def apply(code: String): Either[NoSuccess, List[Token]] = {
    parse(tokens, code) match {
      case err: NoSuccess => Left(err)
      case Success(result, _) => Right(result)
    }
  }

  object Tokens {

    class Token(name: String) extends Positional {
      override def toString: String = name
    }

    case class Or() extends Token("\\/")

    case class And() extends Token("/\\")

    case class Implies() extends Token("->")

    case class Not() extends Token("~")

    case class Equals() extends Token("==")

    case class Exists() extends Token("\\exists")

    case class Union() extends Token("\\union")

    case class Inter() extends Token("\\inter")

    case class Successor1() extends Token("\\succ")

    case class Next1() extends Token("\\++")

    case class Successor2() extends Token("\\SUCC")

    case class Forall() extends Token("\\forall")

    case class In() extends Token("\\in")

    case class Identifier(name: String) extends Token(":identifier")

    // Sugar
    case class IntLiteral(value: Int) extends Token(":intLiteral")

    case class LBrack() extends Token("{")

    case class RBrack() extends Token("}")

    case class LPar() extends Token("(")

    case class RPar() extends Token(")")

    case class LSq() extends Token("[")

    case class RSq() extends Token("]")

    case class Semicolon() extends Token(";")

    case class Colon() extends Token(":")

    case class Comma() extends Token(",")

    case class Def() extends Token("def")

    case class Plus() extends Token("+")

    case class Times() extends Token("*")

    case class Lift() extends Token("lift")

    case class True() extends Token("True")

    case class False() extends Token("False")
  }

}
