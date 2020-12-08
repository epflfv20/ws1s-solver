package ch.epfl.fv20.ws1s

import Kernel._
import automata._

object Solver {
  // Solves if a WS1S formula is valid/satisfiable or not.
  // Essentially means implementing the transformation into an Automata
  def transform(formula: Formula): (Automaton[Int], List[Variable]) =
    (transformWithFreeVar(formula, formula.freeVariables.toList), formula.freeVariables.toList)

  def transformWithFreeVar(formula: Formula, fv: List[Variable]): Automaton[Int] = formula match {
    case subset(l, r) => {
      val states = Set(0)
      val alphabet = Set("00", "01", "10", "11")
      val transitions = Set((0, "00", 0), (0, "01", 0), (0, "11", 0))
      val initial = 0
      val accepting = Set(0)
      Automaton[Int](states, alphabet, transitions, initial, accepting)
    }
    case succ(l, r) => {
      val states = Set(0, 1, 2)
      val alphabet = Set("00", "01", "10", "11")
      val transitions = Set((0, "00", 0), (0, "10", 1), (1, "01", 2), (2, "00", 2))
      val initial = 0
      val accepting = Set(2)
      Automaton(states, alphabet, transitions, initial, accepting)
    }
    case or(l, r) => {
      val (automata1, fv1) = transform(not(l))
      val (automata2, fv2) = transform(not(r))
      // TODO: merge fv1 and fv2
      // TODO: reorder the states of the result of product into integers
      automata1.product(automata2).inverse
    }
    case not(f) => transformWithFreeVar(f, f.freeVariables.toList).inverse
    case exists(v, f) => {
      def deleteCharAt(s: String, index: Int): String = {
        if(index == s.size) s.substring(0, index)
        else s.substring(0, index) ++ s.substring(index + 1)
      }
      val (automata, fv) = transform(f)
      val index = fv.indexOf(v)
      val alphabet = automata.alphabet.map(x => deleteCharAt(x, index))
      val transitions = automata.transitions.map(x => (x._1, deleteCharAt(x._2, index), x._3))
      Automaton(automata.states, alphabet, transitions, automata.initial, automata.accepting)
    }
  }
}
