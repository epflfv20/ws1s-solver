package ch.epfl.fv20.ws1s

/*
This is the representation of the top, rich language in which the user can write formulas, integers and values.
What the user can input should be very close to this language, up to syntax.
Boolean terms are then transformed into the much simpler and smaller internal language described in the kernel.
Some translations are direct, other are less trivial.
 */

object Language {

  def findFreshName(s:Set[String], v:String): String = {
    if (s contains v) findFreshName(s, v+"'") else v
  }


  abstract sealed class Value1(){ //First order values (integers with successor)
    def freeVariables : Set[Variable] = this match {
      case Variable1(name) => Set(Variable1(name))
      case Successor(v) => v.freeVariables
      case Constant1(n) => Set()
      case Plus_n(v, n) => v.freeVariables
    }
    def substitute(v:Variable1, w:Value1) : Value1 = this match {
      case Variable1(name) => if (name == v.name) w else this
      case Successor(v1) =>Successor(v1.substitute(v, w))
      case Constant1(n) =>this
      case Plus_n(v1, n) =>Plus_n(v1.substitute(v, w), n)
    }
  }

  abstract sealed class Value2(){ //Second order values (finite sets)
    def freeVariables : Set[Variable] = this match {
      case Variable2(name) => Set(Variable2(name))
      case ConstantPredicate(s) => s.flatMap((f:Value1) => f.freeVariables )
      case Union(l, r) =>l.freeVariables union r.freeVariables
      case Intersection(l, r) =>l.freeVariables union r.freeVariables
      case ConstantInteger2(n) =>Set()
      case Sum(l, r) =>l.freeVariables union r.freeVariables
      case Product(l, n) =>l.freeVariables
    }
    def substitute(v:Variable1, w:Value1): Value2 = this match {
      case Variable2(name) => this
      case ConstantPredicate(s) => ConstantPredicate(s.map(f => f.substitute(v, w)))
      case Union(l, r) => Union(l.substitute(v, w), r.substitute(v ,w))
      case Intersection(l, r) => Intersection(l.substitute(v, w), r.substitute(v ,w))
      case ConstantInteger2(n) =>this
      case Sum(l, r) =>Sum(l.substitute(v, w), r.substitute(v ,w))
      case Product(l, r) =>l.substitute(v, w)
    }
    def substitute(v:Variable2, w:Value2): Value2 = this match {
      case Variable2(name) => if (name == v.name) w else this
      case ConstantPredicate(s) => this
      case Union(l, r) => Union(l.substitute(v, w), r.substitute(v ,w))
      case Intersection(l, r) => Intersection(l.substitute(v, w), r.substitute(v ,w))
      case ConstantInteger2(n) =>this
      case Sum(l, r) =>Sum(l.substitute(v, w), r.substitute(v ,w))
      case Product(l, r) =>l.substitute(v, w)
    }
  }
  abstract sealed class Boolean(){
    def freeVariables : Set[Variable] = this match {
      case T => Set()
      case F =>Set()
      case Equal1(l, r) =>l.freeVariables union r.freeVariables
      case Succ1(l, r) =>l.freeVariables union r.freeVariables
      case Equal2(l, r) =>l.freeVariables union r.freeVariables
      case Succ2(l, r) =>l.freeVariables union r.freeVariables
      case Subset(l, r) =>l.freeVariables union r.freeVariables
      case And(l, r) =>l.freeVariables union r.freeVariables
      case Or(l, r) =>l.freeVariables union r.freeVariables
      case Not(b) =>b.freeVariables
      case Exists(v, b) =>b.freeVariables - v
      case Forall(v, b) =>b.freeVariables - v
    }
    def substitute(v:Variable1, w:Value1): Boolean = this match {
      case Equal1(l, r) => Equal1(l.substitute(v, w), r.substitute(v, w))
      case Succ1(l, r) => Succ1(l.substitute(v, w), r.substitute(v, w))
      case Equal2(l, r) =>Equal2(l.substitute(v, w), r.substitute(v, w))
      case Succ2(l, r) =>Succ2(l.substitute(v, w), r.substitute(v, w))
      case Subset(l, r) =>Subset(l.substitute(v, w), r.substitute(v, w))
      case And(l, r) =>And(l.substitute(v, w), r.substitute(v, w))
      case Or(l, r) =>Or(l.substitute(v, w), r.substitute(v, w))
      case Not(b) =>Not(b.substitute(v, w))

      case Exists(v1: Variable1, b) => if (v1 == v) this else if (w.freeVariables.contains(v1)) { //capture-avoiding substitution
        val taken = (w.freeVariables + v).map { case Variable1(name) => name; case Variable2(name) => name }
        val nv = Variable1(findFreshName(taken, v1.name))
        Exists(nv, b.substitute(v1, nv).substitute(v, w))
      } else Exists(v1, b.substitute(v, w))

      case Forall(v1: Variable1, b) => if (v1 == v) this else if (w.freeVariables.contains(v)) { //capture-avoiding substitution
        val taken = (w.freeVariables + v).map { case Variable1(name) => name; case Variable2(name) => name }
        val nv = Variable1(findFreshName(taken, v1.name))
        Forall(nv, b.substitute(v1, nv).substitute(v, w))
      } else Forall(v1, b.substitute(v, w))

      case Exists(v1:Variable2, b) => Exists(v1, b.substitute(v, w))
      case Forall(v1:Variable2, b) => Forall(v1, b.substitute(v, w))
      case _ => this
    }
    def substitute(v:Variable2, w:Value2): Boolean = this match {
      case Equal2(l, r) =>Equal2(l.substitute(v, w), r.substitute(v, w))
      case Succ2(l, r) =>Succ2(l.substitute(v, w), r.substitute(v, w))
      case Subset(l, r) =>Subset(l.substitute(v, w), r.substitute(v, w))
      case And(l, r) =>And(l.substitute(v, w), r.substitute(v, w))
      case Or(l, r) =>Or(l.substitute(v, w), r.substitute(v, w))
      case Not(b) =>Not(b.substitute(v, w))

      case Exists(v1: Variable2, b) => if (v1 == v) this else if (w.freeVariables.contains(v1)) { //capture-avoiding substitution
        val taken = (w.freeVariables + v).map { case Variable1(name) => name; case Variable2(name) => name }
        val nv = Variable2(findFreshName(taken, v1.name))
        Exists(nv, b.substitute(v1, nv).substitute(v, w))
      } else Exists(v1, b.substitute(v, w))

      case Forall(v1: Variable2, b) => if (v1 == v) this else if (w.freeVariables.contains(v)) { //capture-avoiding substitution
        val taken = (w.freeVariables + v).map { case Variable1(name) => name; case Variable2(name) => name }
        val nv = Variable2(findFreshName(taken, v1.name))
        Forall(nv, b.substitute(v1, nv).substitute(v, w))
      } else Forall(v1, b.substitute(v, w))

      case Exists(v1:Variable1, b) => Exists(v1, b.substitute(v, w))
      case Forall(v1:Variable1, b) => Forall(v1, b.substitute(v, w))

      case _ => this
    }

    def instantiateBooleanVariable(v:VariableB, w:Boolean): Boolean = this match {
      case And(l, r) =>And(l.instantiateBooleanVariable(v, w), r.instantiateBooleanVariable(v, w))
      case Or(l, r) =>Or(l.instantiateBooleanVariable(v, w), r.instantiateBooleanVariable(v, w))
      case Not(b) =>Not(b.instantiateBooleanVariable(v, w))
      case Exists(v1,b) => b.instantiateBooleanVariable(v, w)
      case Forall(v1,b) => b.instantiateBooleanVariable(v, w)
      case v1 : VariableB =>if (v1 == v) w else v1
      case _ => this
    }

  }
  trait Variable

  case class Variable1(name: String) extends Value1 with Variable //First order variable
  case class Successor(v:Value1) extends Value1
  case class Constant1(n:Int) extends Value1
  case class Plus_n(v:Value1, n:Constant1) extends Value1

  case class Variable2(name:String) extends Value2 with Variable //second order variable
  case class ConstantPredicate(s: Set[Value1]) extends Value2
  case class Union(l: Value2, r: Value2) extends Value2
  case class Intersection(l: Value2, r: Value2) extends Value2

  case class ConstantInteger2(n: Int) extends Value2
  case class Sum(l: Value2, r: Value2) extends Value2
  case class Product(l: Value2, n: ConstantInteger2) extends Value2

  object T extends Boolean
  object F extends Boolean
  case class VariableB(name:String) extends Boolean
  case class Equal1(l:Value1, r:Value1) extends Boolean
  case class Succ1(l:Value1, r:Value1) extends Boolean

  case class In(l:Value1, r:Value2) extends Boolean

  case class Equal2(l:Value2, r:Value2) extends Boolean
  case class Succ2(l:Value2, r:Value2) extends Boolean
  case class Subset(l:Value2, r:Value2) extends Boolean

  case class And(l: Boolean, r:Boolean) extends Boolean
  case class Or(l:Boolean, r:Boolean) extends Boolean
  case class Not(b: Boolean) extends Boolean
  case class Exists (v:Variable, b:Boolean) extends Boolean
  case class Forall(v:Variable, b:Boolean) extends Boolean

}
