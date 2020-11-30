package ch.epfl.fv20.ws1s


import scala.util.Success
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

  def or = positioned {
    ("||" | "\\/") ^^^ Or()
  }

  def and = positioned {
    ("&&" | "/\\") ^^^ And()
  }

  def not = positioned {
    ("!" | "~") ^^^ Not()
  }

  def equals = positioned {
    ("==") ^^^ Equals()
  }

  def exists = positioned {
    ("\\exists" | "\\E") ^^^ Exists()
  }

  def in = positioned {
    ("\\subsetof" | "\\in") ^^^ In()
  }

  def succ = positioned {
    ("\\succ" | "++") ^^^ Successor()
  }

  def lpar = positioned("(" ^^^ LPar())

  def rpar = positioned(")" ^^^ RPar())

  def lbrack = positioned("{" ^^^ LBrack())

  def rbrack = positioned("}" ^^^ RBrack())

  def semicolon = positioned(";" ^^^ Semicolon())

  def colon = positioned(":" ^^^ Colon())

  def tokens: Parser[List[Token]] = {
    phrase(
      rep1(positioned(id | lbrack | rbrack | lpar | rpar | and | or | equals | not | exists | in | colon | semicolon))
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

    case class Not() extends Token("~")

    case class Equals() extends Token("==")

    case class Exists() extends Token("\\exists")

    case class Successor() extends Token("\\succ")

    case class Forall() extends Token("\\forall")

    case class In() extends Token("\\in")

    case class Identifier(name: String) extends Token(":identifier")

    // Sugar
    case class IntLiteral(value: Int) extends Token(":intLiteral")

    case class LBrack() extends Token("{")

    case class RBrack() extends Token("}")

    case class LPar() extends Token("(")

    case class RPar() extends Token(")")

    case class Semicolon() extends Token(";")

    case class Colon() extends Token(":")

  }

}
