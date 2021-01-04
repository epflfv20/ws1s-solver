package ch.epfl.fv20.ws1s

import ch.epfl.fv20.ws1s.Kernel._
import ch.epfl.fv20.ws1s.Lexer.Tokens
import ch.epfl.fv20.ws1s.Lexer.Tokens._

import scala.collection.mutable
import scala.io.StdIn
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.{NoPosition, Position, Reader}

/*
This file is the exact same as the other one with "Value" renamed "Variable" and still compile.
It should parse the user input into a tree as described in Language, as the process of implementing first and second order values is much too complex to be
directly implemented from the input text into the Kernel. Technically, this is the parser and the file "Translator" really is the interpreter.
 */
object Interpreter2 {


  object Parser extends Parsers {

    case class Macro(name: String, args: List[String], formula: Formula)

    private val macros: mutable.Map[String, Macro] = new mutable.HashMap[String, Macro]()

    override type Elem = Tokens.Token

    def substitute(variable: String, value: Variable, formula: Formula): Formula = {
      def substituteVariable(variable: String, value: Variable, substIn: Variable): Variable = {
        value match {
          case Variable(name) if name == variable => value
          case other => other
        }
      }

      formula match {
        case subset(l: Variable, r: Variable) =>
          subset(substituteVariable(variable, value, l), substituteVariable(variable, value, r))

        case succ(l: Variable, r: Variable) =>
          succ(substituteVariable(variable, value, l), substituteVariable(variable, value, r))

        case or(l: Formula, r: Formula) =>
          or(substitute(variable, value, l), substitute(variable, value, r))

        case not(f: Formula) =>
          Kernel.not(substitute(variable, value, f))

        case exists(v: Variable, f: Formula) =>
          // We "declare" a new variable on the LHS, therefore we should not replace the variable on this side
          exists(v, substitute(variable, value, f))
      }
    }

    def identifier: Parser[Variable] = {
      accept("identifier", {
        case Identifier(name) => Variable(name)
      })
    }

    def macrodef: Parser[Macro] = {
      (Def() ~ identifier ~ LPar() ~ repsep(identifier, accept(Comma())) ~ RPar() ~ Colon() ~ operation) ^^ {
        case _ ~ id ~ _ ~ args ~ _ ~ _ ~ formula => Macro(id.name, args.map(_.name), formula)
      }
    }

    def operation: Parser[Formula] = {
      def par = (LPar() ~! operation ~! RPar() ^^ { case _ ~ f ~ _ => f })

      def not = Not() ~! operation ^^ { case _ ~ e => Kernel.not(e) }

      def value: Parser[Variable] = identifier

      def varOps = {
        def macroUse: Parser[Variable => Formula] = {
          (LPar() ~> repsep(value, accept(Comma())) <~ RPar()) ^^ {
            case values =>
              // Anonymous function Variable => Formula
              {
                case Variable(name) =>
                  if (!macros.contains(name)) throw new Exception("Invalid macro " + name)

                  val macr = macros(name)

                  if (macr.args.length != values.length) throw new Exception("Invalid number of arguments for macro " + name + "(" + macr.args.mkString(", ") + ")")

                  macr.args.zip(values).foldLeft(macr.formula)((formula, nameVariablePair) => substitute(nameVariablePair._1, nameVariablePair._2, formula))
                case _ => throw new Exception("Invalid function call with a non identifier token")
              }
          }

        }

        def varOperations: Parser[Variable => Formula] = ((In() | Equals()) ~ value) ^^ {
          case Equals() ~ r => l => equ(l, r)
          case In() ~ r => l => subset(l, r)
          case Successor() ~ r => l => succ(l, r)
        }

        value ~ (macroUse | varOperations) ^^ {
          case value ~ func => func(value)
        }
      }


      def quantifiers = ((Forall() | Exists()) ~ identifier ~ Colon() ~ operation) ^^ {
        case Forall() ~ id ~ _ ~ op => forall(id, op)
        case Exists() ~ id ~ _ ~ op => exists(id, op)
      }

      def formula = par | not | varOps | quantifiers

      def combinations: Parser[Formula] = chainl1(formula, combinations, (And() | Or() | Implies()) ^^ {
        case And() => (l: Formula, r: Formula) => and(l, r)
        case Or() => (l: Formula, r: Formula) => or(l, r)
        case Implies() => (l: Formula, r: Formula) => or(Kernel.not(l), r)
      })

      combinations
    }

    // TODO: definition of an "alias" (isolated part of a formula that can be reused)
    // TODO: sequence of expressions (seq of aliases followed by a final formula)
    // TODO: check free variables in a formula

    class TokenReader(tokens: Seq[Token]) extends Reader[Token] {
      override def first: Token = tokens.head

      override def rest: Reader[Token] = new TokenReader(tokens.tail)

      override def pos: Position = if (atEnd) NoPosition else first.pos

      override def atEnd: Boolean = tokens.isEmpty
    }

    def apply(tokens: Seq[Token]): Either[NoSuccess, Either[Formula, Macro]] = {
      phrase((operation | macrodef) ^^ {
        case m: Macro => Right(m)
        case f: Formula => Left(f)
      })(new TokenReader(tokens)) match {
        case Success(result: Either[Formula, Macro], next) =>
          if (result.isRight) {
            val macr = result.right.get
            macros.put(macr.name, macr)
          }

          Right(result)
        case ns: NoSuccess => Left(ns)
      }
    }
  }

  def main(args: Array[String]): Unit = {
    while (true) {
      print("Formula? > ")
      val form = StdIn.readLine()
      Lexer(form).map(r => {println(r) ; r}).flatMap(tokens => Parser.apply(tokens)) match {
        case Left(err) => println("Error at " + err.next.pos + ": " + err.msg)
        case Right(Left(f)) => println("Formula: " + f)
        case Right(Right(m)) => println("New macro " + m.name)
      }
    }

  }

  //objective is to ask user for input formula and parse it
}
