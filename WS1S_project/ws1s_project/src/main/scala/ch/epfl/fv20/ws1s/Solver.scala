package ch.epfl.fv20.ws1s

import Kernel._
import Automata._

object Solver {
  // Solves if a WS1S formula is valid/satisfiable or not.
  // Essentially means implementing the transformation into an Automaton
  def generateAlphabet(n: Int): Set[String] = n match {
    case 0 => Set("0", "1")
    case 1 => Set("0", "1")
    case n => generateAlphabet(n - 1).flatMap(x => Set("0" + x, "1" + x))
  }

  def sameVars(varList: List[Variable]) =
    varList.forall(v => v.name == varList.head.name)

  def sameFormulae(l: Formula, boundVarL: List[Variable], r: Formula, boundVarR: List[Variable]): Boolean = (l, r) match {
    case (subset(xl, yl), subset(xr, yr)) => {
      if(boundVarL.contains(xl) && boundVarR.contains(xr) && boundVarL.indexOf(xl) == boundVarR.indexOf(xr)) {
        if(boundVarL.contains(yl) && boundVarR.contains(yr) && boundVarL.indexOf(yl) == boundVarR.indexOf(yr)) {
          true
        }
        else {
          yl.name == yr.name
        }
      }
      else {
        xl.name == xr.name && yl.name == yr.name
      }
    }
    case (succ(xl, yl), succ(xr, yr)) => sameVars(List(xl, xr)) && sameVars(List(yl, yr))
    case (or(xl, yl), or(xr, yr)) => sameFormulae(xl, boundVarL, xr, boundVarR) && sameFormulae(yl, boundVarL, yr, boundVarR)
    case (not(fl), not(fr)) => sameFormulae(fl, boundVarL, fr, boundVarR)
    case (exists(vl, fl), exists(vr, fr)) => sameFormulae(fl, vl :: boundVarL, fr, vr :: boundVarR)
    case (Kernel.tr, Kernel.tr) => true
    case _ => false
  }

  def deleteCharAt(s: String, index: Int): String = {
    if(index == s.size) s.substring(0, index)
    else s.substring(0, index) ++ s.substring(index + 1)
  }

  def newAutomaton(au: Automaton[Int], f: List[Variable], alphabet: Set[Symbol], fv: List[Variable]): Automaton[Int] = {
    def extendAlphabet(transitions: Set[(Int, Symbol, Int)], index: List[Int]) = transitions.flatMap(x =>
      alphabet.filter(s => index.map(y => s.charAt(y)).mkString.equals(x._2)).map(s => (x._1, s, x._3)))
    Automaton(au.states, alphabet, extendAlphabet(au.transitions, f.map(x => fv.indexOf(x))), au.initial, au.accepting)
  }

  def reorder[T](automaton: Automaton[T]): Automaton[Int] = {
    val statesOrder = automaton.states.toList
    val states = automaton.states.map(x => statesOrder.indexOf(x))
    val transitions = automaton.transitions.map(x => (statesOrder.indexOf(x._1), x._2, statesOrder.indexOf(x._3)))
    val initial = statesOrder.indexOf(automaton.initial)
    val accepting = automaton.accepting.map(x => statesOrder.indexOf(x))
    Automaton(states, automaton.alphabet, transitions, initial, accepting)
  }

  def transform(formula: Formula): (Automaton[Int], List[Variable]) =
    (transformWithFreeVar(formula, formula.freeVariables.toList), formula.freeVariables.toList)

  def transformWithFreeVar(formula: Formula, fv: List[Variable]): Automaton[Int] = {
    formula match {
      case Kernel.tr => {
        val states = Set(0)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "0", 0), (0, "1", 0))
        val initial = 0
        val accepting = Set(0)
        Automaton[Int](states, alphabet, transitions, initial, accepting)
      }
      case not(not(f)) => transformWithFreeVar(f, fv)
      // singleton
      case singleton(_)=> {
        val states = Set(0, 1)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "0", 0), (0, "1", 1), (1, "0", 1))
        val initial = 0
        val accepting = Set(1)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // set equal
      case equal(l1, r1)  =>{
        val states = Set(0)
        val alphabet = generateAlphabet(2)
        val transitions = Set((0, "00", 0), (0, "11", 0))
        val initial = 0
        val accepting = Set(0)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // is_empty
      case is_empty(_) => {
        val states = Set(0)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "0", 0))
        val initial = 0
        val accepting = Set(0)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // zero_th
      case zeroth(_) => {
        val states = Set(0, 1)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "1", 1), (1, "0", 1))
        val initial = 0
        val accepting = Set(1)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // iff
      case iff(l1, r1) => {
        val (automaton1, fv1) = transform(l1)
        val (automaton2, fv2) = transform(r1)
        val alphabet = generateAlphabet(fv.size)
        val l2r = reorder(newAutomaton(automaton1, fv1, alphabet, fv).product(newAutomaton(automaton2.inverse, fv2, alphabet, fv)).minimiseState()).inverse
        val r2l = reorder(newAutomaton(automaton1.inverse, fv1, alphabet, fv).product(newAutomaton(automaton2, fv2, alphabet, fv)).minimiseState()).inverse
        reorder(l2r.product(r2l).minimiseState())
      }
      case subset(_, _) => {
        val states = Set(0)
        val alphabet = generateAlphabet(2)
        val transitions = Set((0, "00", 0), (0, "01", 0), (0, "11", 0))
        val initial = 0
        val accepting = Set(0)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      case succ(_, _) => {
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
        reorder(newAutomaton(automaton1, fv1, alphabet, fv).product(newAutomaton(automaton2, fv2, alphabet, fv)).minimiseState()).inverse
      }
      case and(l, r) => {
        val (automaton1, fv1) = transform(l)
        val (automaton2, fv2) = transform(r)
        val alphabet = generateAlphabet(fv.size)
        reorder(newAutomaton(automaton1, fv1, alphabet, fv).product(newAutomaton(automaton2, fv2, alphabet, fv)).minimiseState())
      }
      case not(f) => transformWithFreeVar(f, f.freeVariables.toList).inverse
      case exists(v, f) => {
        val (automaton, fv) = transform(f)
        val index = fv.indexOf(v)
        val alphabet = automaton.alphabet.map(x => deleteCharAt(x, index))
        val transitions = automaton.transitions.map(x => (x._1, deleteCharAt(x._2, index), x._3))
        Automaton(automaton.states, alphabet, transitions, automaton.initial, automaton.accepting)
      }
    }
  }

  def main(args: Array[String]): Unit = {
    val f = or(subset(Variable("X"), Variable("Y")), subset(Variable("X"), Variable("Z")))
    val f1 = singleton(Variable("x"))
    val f2 = is_empty(Variable("x"))
    val eq = equal(Variable("X"), Variable("Y"))
    val f3 = iff(subset(Variable("X"), Variable("Y")), subset(Variable("Y"), Variable("X")))
    val sing = singleton(Variable("X"))
  }
}
