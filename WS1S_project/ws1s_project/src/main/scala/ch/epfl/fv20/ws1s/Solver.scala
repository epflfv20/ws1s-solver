package ch.epfl.fv20.ws1s

import Kernel._
import automata._

object Solver {
  // Solves if a WS1S formula is valid/satisfiable or not.
  // Essentially means implementing the transformation into an Automaton
  def generateAlphabet(n: Int): Set[String] = n match {
    case 1 => Set("0", "1")
    case n => generateAlphabet(n - 1).flatMap(x => Set("0" + x, "1" + x))
  }

  def transform(formula: Formula): (Automaton[Int], List[Variable]) =
    (transformWithFreeVar(formula, formula.freeVariables.toList), formula.freeVariables.toList)

  def transformWithFreeVar(formula: Formula, fv: List[Variable]): Automaton[Int] = formula match {
    case subset(l, r) => {
      val states = Set(0)
      val alphabet = generateAlphabet(2)
      val transitions = Set((0, "00", 0), (0, "01", 0), (0, "11", 0))
      val initial = 0
      val accepting = Set(0)
      Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
    }
    case succ(l, r) => {
      val states = Set(0, 1, 2)
      val alphabet = generateAlphabet(2)
      val transitions = Set((0, "00", 0), (0, "10", 1), (1, "01", 2), (2, "00", 2))
      val initial = 0
      val accepting = Set(2)
      Automaton(states, alphabet, transitions, initial, accepting).make_total(states.size)
    }
    case or(l, r) => {
      val (automaton1, fv1) = transform(not(l))
      val (automaton2, fv2) = transform(not(r))
      val alphabet = generateAlphabet(fv.size)
      def extendAlphabet(transitions: Set[(Int, Symbol, Int)], index: List[Int]) = transitions.flatMap(x =>
          alphabet.filter(s => index.map(y => s.charAt(y)).mkString.equals(x._2)).map(s => (x._1, s, x._3)))
      def newAutomaton(au: Automaton[Int], f: List[Variable]) = {
        println(extendAlphabet(au.transitions, f.map(x => fv.indexOf(x))))
        println(f.map(x => fv.indexOf(x)).map(y => "001".charAt(y)).mkString)
        Automaton(au.states, alphabet, extendAlphabet(au.transitions, f.map(x => fv.indexOf(x))), au.initial, au.accepting)
      }
      def reorder(automaton: Automaton[(Int, Int)]): Automaton[Int] = {
        val statesOrder = automaton.states.toList
//        println(statesOrder)
//        println(automaton.transitions)
        val states = automaton.states.map(x => statesOrder.indexOf(x))
        val transitions = automaton.transitions.map(x => (statesOrder.indexOf(x._1), x._2, statesOrder.indexOf(x._3)))
//        println(transitions)
        val initial = statesOrder.indexOf(automaton.initial)
        val accepting = automaton.accepting.map(x => statesOrder.indexOf(x))
        Automaton(states, automaton.alphabet, transitions, initial, accepting)
      }
//      val n1 = newAutomaton(automaton1, fv1)
//      val n2 = newAutomaton(automaton2, fv2)
//      println(n1, n2)
      reorder(newAutomaton(automaton1, fv1).product(newAutomaton(automaton2, fv2))).inverse
    }
    case not(f) => transformWithFreeVar(f, f.freeVariables.toList).inverse
    case exists(v, f) => {
      def deleteCharAt(s: String, index: Int): String = {
        if(index == s.size) s.substring(0, index)
        else s.substring(0, index) ++ s.substring(index + 1)
      }
      val (automaton, fv) = transform(f)
      val index = fv.indexOf(v)
      val alphabet = automaton.alphabet.map(x => deleteCharAt(x, index))
      val transitions = automaton.transitions.map(x => (x._1, deleteCharAt(x._2, index), x._3))
      Automaton(automaton.states, alphabet, transitions, automaton.initial, automaton.accepting)
    }
  }

  def main(args: Array[String]): Unit = {
    val f = or(subset(Variable("X"), Variable("Y")), subset(Variable("X"), Variable("Z")))
    println(transform(f))
  }
}
