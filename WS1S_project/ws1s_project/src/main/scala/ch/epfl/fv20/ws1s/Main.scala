package ch.epfl.fv20.ws1s

import ch.epfl.fv20.ws1s.CustomParser.Parser

import scala.io.StdIn

object Main {
  def main(args: Array[String]): Unit = {
    while (true) {
      print("Formula? > ")
      val form = StdIn.readLine()
      Lexer(form).flatMap(tokens => Parser.apply(tokens)) match {
        case Left(err) => println("Parse Error at " + err.next.pos + ": " + err.msg)
        case Right(Left(f)) =>
          val result = Interpreter.translateAndSolve(f)
          println(s"Result: $result")
        case Right(Right(m)) => println("New macro added " + m.name)
      }
    }

  }
}
