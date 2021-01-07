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

  def sameVars(varList: List[Variable]): Boolean =
    varList.forall(v => v.name == varList.head.name)

  def sameFormulae(l: Formula, boundVarL: List[Variable], r: Formula, boundVarR: List[Variable]): Boolean = (l, r) match {
    case (subset(xl, yl), subset(xr, yr)) =>
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
    case (succ(xl, yl), succ(xr, yr)) => sameVars(List(xl, xr)) && sameVars(List(yl, yr))
    case (or(xl, yl), or(xr, yr)) => sameFormulae(xl, boundVarL, xr, boundVarR) && sameFormulae(yl, boundVarL, yr, boundVarR)
    case (not(fl), not(fr)) => sameFormulae(fl, boundVarL, fr, boundVarR)
    case (exists(vl, fl), exists(vr, fr)) => sameFormulae(fl, vl :: boundVarL, fr, vr :: boundVarR)
    case (Kernel.tr, Kernel.tr) => true
    case _ => false
  }

  def deleteCharAt(s: String, index: Int): String = {
    if(index == s.length) s.substring(0, index)
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
      // singleton
//      case not(or(not(exists(x1,not(subset(y1, x2)))),exists(x3,not(or(not(subset(x4,y2)),not(or(not(not(exists(z1,not(subset(x5,z2))))),not(subset(y3,x6)))))))))
//        if(sameVars(List(x1, x2, x3, x4, x5, x6)) && sameVars(List(y1, y2, y3)) && sameVars(List(z1, z2))) => {
//        val states = Set(0, 1)
//        val alphabet = generateAlphabet(1)
//        val transitions = Set((0, "0", 0), (0, "1", 1), (1, "0", 1))
//        val initial = 0
//        val accepting = Set(1)
//        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
//      }
      // set equal
      case not(or(not(subset(l1, r1)), not(subset(l2, r2))))
        if(sameVars(List(l1, r2)) && sameVars(List(l2, r1))) => {
        val states = Set(0)
        val alphabet = generateAlphabet(2)
        val transitions = Set((0, "00", 0), (0, "11", 0))
        val initial = 0
        val accepting = Set(0)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // is_empty
      case not(exists(y1, not(subset(y2, _)))) if(sameVars(List(y1, y2))) => {
        val states = Set(0)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "0", 0))
        val initial = 0
        val accepting = Set(0)
        val a = Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
        println(a)
        a
      }
      // zero_th
      case not(or(not(not(or(not(exists(x1,not(subset(x2,y1)))),exists(x3,not(or(not(subset(x4,y2)),not(or(not(not(exists(z1,not(subset(z2,x5))))),not(subset(y3,x6)))))))))),not(not(exists(w1,not(not(succ(w2,y4))))))))
        if(sameVars(List(x1, x2, x3, x4, x5, x6)) && sameVars(List(y1, y2, y3, y4)) && sameVars(List(z1, z2)) && sameVars(List(w1, w2))) => {
        val states = Set(0, 1)
        val alphabet = generateAlphabet(1)
        val transitions = Set((0, "1", 1), (1, "0", 1))
        val initial = 0
        val accepting = Set(1)
        Automaton[Int](states, alphabet, transitions, initial, accepting).make_total(states.size)
      }
      // iff
      case not(or(not(or(not(l1),r1)),not(or(not(r2),l2))))
        if(sameFormulae(l1, List(), l2, List()) && sameFormulae(r1, List(), r2, List())) => {
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
      case not(f) =>
        {
          val a = transformWithFreeVar(f, fv)
          println(f, a)
          a.inverse
        }
      case exists(v, f) => {
        val (automaton, fv) = transform(f)
        val index = fv.indexOf(v)
        val alphabet = automaton.alphabet.map(x => deleteCharAt(x, index))
        val transitions = automaton.transitions.map(x => (x._1, deleteCharAt(x._2, index), x._3))
        val auto = Automaton(automaton.states, alphabet, transitions, automaton.initial, automaton.accepting)
        if(auto.is_deterministic()) auto else reorder(auto.deterministicalize())
      }
    }
  }

  def pathSearch(automaton: Automaton[Int], fv: List[Variable]): Option[Map[Variable, String]] = {
    @scala.annotation.tailrec
    def bfs(pending: List[(Int, List[String])], unchecked: Set[Int]): Option[List[String]] = pending match {
      case h :: _ if(automaton.accepting.contains(h._1)) => Some(h._2)
      case h :: t => {
        val nextStates = (for {s <- automaton.alphabet} yield (automaton.next(h._1, s), h._2 :+ s)).filter(x => unchecked contains x._1)
        bfs(t ++ nextStates, unchecked diff nextStates.map(x => x._1))
      }
      case Nil => None
    }

    @scala.annotation.tailrec
    def makeMap(fv: List[Variable], assign: List[String], map: Map[Variable, String]): Map[Variable, String] = fv match {
      case h :: t => {
        val assignRemain = assign.map(x => x.tail)
        val s = assign.foldLeft("")((b, x) => b + x.head)
        makeMap(t, assignRemain, map + (h -> s))
      }
      case Nil => map
    }

    val assignment = bfs(List((automaton.initial, List())), automaton.states - automaton.initial)
    assignment match {
      case Some(assign) => Some(makeMap(fv, assign, Map()))
      case None => None
    }
  }

  def solve(formula: Formula): Option[Map[Variable, String]] = {
    val automaton = transform(formula)
    println(automaton)
    pathSearch(automaton._1, automaton._2)
  }

  def main(args: Array[String]): Unit = {
    val f = or(subset(Variable("X"), Variable("Y")), subset(Variable("X"), Variable("Z")))
    val f1 = singleton(Variable("x"))
    val f2 = is_empty(Variable("x"))
    val eq = equ(Variable("X"), Variable("Y"))
    val f3 = iff(subset(Variable("X"), Variable("Y")), subset(Variable("Y"), Variable("X")))
    val noSol = and(subset(Variable("X"), Variable("Y")), not(subset(Variable("X"), Variable("Y"))))
    val sing = ~or(is_empty(Variable("X")), exists(Variable("Y"), subset(Variable("Y"), Variable("X"))  /\ (~is_empty(Variable("Y")) \/ ~subset(Variable("X"), Variable("Y")))))
    val ff = exists(Variable("Y"), succ(Variable("Y"), Variable("X")))// /\
    val ff1 = exists(Variable("Y"), subset(Variable("Y"), Variable("X"))  /\ (~is_empty(Variable("Y")) \/ ~subset(Variable("X"), Variable("Y"))))
//    println(ff1)
    println(solve(singleton(Variable("Y"))))
//    println(solve(ff1))
  }
}
