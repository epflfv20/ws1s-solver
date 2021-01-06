package ch.epfl.fv20.ws1s

import Language._
object Simplifier {

  //simplify1 combine recursively some simple formula simplifications, like replacing x=x by T, or ~~f by f, n+0 by n, etc.
  def simplify1(f:Value1): Value1 = f match {
    case Plus_n(v, Constant1(0)) => v

    case Successor(v) =>Successor(simplify1(v))
    case Plus_n(v, n) =>Plus_n( simplify1(v), n)
    case _ => f
  }

  def simplify1(f:Value2): Value2 = f match {
    case Sum(v, ConstantInteger2(0)) => v
    case Sum(ConstantInteger2(0), v) => v
    case Union(v, w) => if (v == w) v else f
    case Union(v, ConstantPredicate(s)) => if (s.isEmpty) v else f
    case Intersection(v, w) => if (v == w) v else f
    case Intersection(v, ConstantPredicate(s)) => if (s.isEmpty) ConstantPredicate(s) else f

    case Intersection(l, r) => Sum(simplify1(l), simplify1(r))
    case Sum(l, r) => Sum(simplify1(l), simplify1(r))
    case Union(l, r) => Sum(simplify1(l), simplify1(r))
    case ConstantPredicate(s) =>ConstantPredicate(s.map(t => simplify1(t)))
    case Product(l, n) =>Product(simplify1(l), n)
    case _ => f
  }

  def simplify1(f:BooleanFormula): BooleanFormula = f match {
    case Equal2(v, w) => if (v == w) T else f
    case Equal2(v, w) => Equal2(simplify1(v), simplify1(w))
    case And(T, w) => simplify1(w)
    case And(v, T) => simplify1(v)
    case And(F, w) => F
    case And(v, F) => F
    case And(v, w) => if (v == w) simplify1(v) else And(simplify1(v), simplify1(w))
    case Or(T, w) => T
    case Or(v, T) => T
    case Or(F, w) => simplify1(w)
    case Or(v, F) => simplify1(v)
    case Or(v, w) => if (v == w) simplify1(v) else Or(simplify1(v), simplify1(w))
    case Not(Not(v)) => simplify1(v)
    case Not(F) => T
    case Not(T) => F

    case Equal1(l, r) =>Equal1(simplify1(l), simplify1(r))
    case Succ1(l, r) => Succ1(simplify1(l), simplify1(r))
    case Succ2(l, r) => Succ2(simplify1(l), simplify1(r))
    case Subset(l, r) => Subset(simplify1(l), simplify1(r))
    case Exists(v, b) => Exists(v, simplify1(b))
    case Forall(v, b) => Forall(v, simplify1(b))
    case _ => f

  }
  def searchEqInAnd(f:BooleanFormula, v:Variable1): (Option[Equal1], BooleanFormula) = f match {
    case And(l, r) =>{
      val e1 = searchEqInAnd(l, v)
      val e2 = searchEqInAnd(r, v)
      if (e1._1.isDefined) (e1._1, And(e1._2, r)) else (e2._1, And(l, e2._2))
    }
    case Equal1(`v`, Variable1(s)) => (Some(Equal1(v, Variable1(s))), T)
    case Equal1(Variable1(s), `v`) => (Some(Equal1(Variable1(s), v)), T)
    case _ => (None, f)
  }
  def searchEqInAnd(f:BooleanFormula, v:Variable2): (Option[Equal2], BooleanFormula) = f match {
    case And(l, r) =>{
      val e1 = searchEqInAnd(l, v)
      val e2 = searchEqInAnd(r, v)
      if (e1._1.isDefined) (e1._1, And(e1._2, r)) else (e2._1, And(l, e2._2))
    }
    case Equal2(`v`, Variable2(s)) => (Some(Equal2(v, Variable2(s))), T)
    case Equal2(Variable2(s), `v`) => (Some(Equal2(Variable2(s), v)), T)
    case _ => (None, f)
  }


  //simplify 2 looks for redundant existential quantifiers. Should maybe also be implemented at the internal level, after transformation, since it introduces new quantifiers.
  def simplify2(f:BooleanFormula): BooleanFormula = f match {
    case Exists(v, b) => {
      v match {
        case v: Variable1 => {
          searchEqInAnd(b, v) match {
            case (Some(Equal1(`v`, w:Variable1)), c) => c.substitute(v, w)
            case (Some(Equal1(w:Variable1, `v`)), c) => c.substitute(v, w)
            case _ => f
          }
        }
        case v: Variable2 =>{
          searchEqInAnd(b, v) match {
            case (Some(Equal2(`v`, w:Variable2)), c) => c.substitute(v, w)
            case (Some(Equal2(w:Variable2, `v`)), c) => c.substitute(v, w)
            case _ => f
          }
        }
      }
    }
    case _ => f
  }

}
