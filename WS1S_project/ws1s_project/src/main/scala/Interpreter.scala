import Kernel._
import Lexer.{Tokens, colon}
import Lexer.Tokens._

import scala.io.StdIn
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.{NoPosition, Position, Positional, Reader}

object Interpreter {

  object Parser extends Parsers {
    override type Elem = Tokens.Token

    def identifier: Parser[Variable] = {
      accept("identifier", {
        case Identifier(name) => Variable(name)
      })
    }

    def operation: Parser[Formula] = {
      def par = (LPar() ~! operation ~! RPar() ^^ { case _ ~ f ~ _ => f })

      def not = Not() ~! operation ^^{ case _ ~ e => Kernel.not(e) }

      def varOperations = (identifier ~ (In() | Equals()) ~ identifier) ^^ {
        case l ~ Equals() ~ r => equ(l, r)
        case l ~ In() ~ r => subset(l, r)
        case l ~ Successor() ~ r => succ(l, r)
      }

      def quantifiers = ((Forall() | Exists()) ~ identifier ~ Colon() ~ operation) ^^ {
        case Forall() ~ id ~ _ ~ op => forall(id, op)
        case Exists() ~ id ~ _ ~ op => exists(id, op)
      }

      def formula = par | not | varOperations | quantifiers

      def combinations: Parser[Formula] = chainl1(formula, combinations, (And() | Or()) ^^ {
        case And() => (l: Formula, r: Formula) => and(l, r)
        case Or() => (l: Formula, r: Formula) => or(l, r)
      })

      combinations
    }

    // TODO: definition of an "alias" (isolated part of a formula that can be reused)
    // TODO: sequence of expressions (seq of aliases followed by a final formula)

    class TokenReader(tokens: Seq[Token]) extends Reader[Token] {
      override def first: Token = tokens.head
      override def rest: Reader[Token] = new TokenReader(tokens.tail)
      override def pos: Position = if (atEnd) NoPosition else first.pos
      override def atEnd: Boolean = tokens.isEmpty
    }

    def apply(tokens: Seq[Token]): Either[NoSuccess, Formula] = {
      positioned(phrase(operation))(new TokenReader(tokens)) match {
        case Success(result, next) => Right(result)
        case ns: NoSuccess => Left(ns)
      }
    }
  }

  def main(args: Array[String]): Unit = {
    print("Formula? > ")
    val form = StdIn.readLine()
    Lexer(form).map(Parser.apply) match {
      case Left(err) => println("Error at " + err.next.pos + ": " + err.msg)
      case Right(form) => println("Formula: " + form)
    }


  }
//objective is to ask user for input formula and parse it
}
