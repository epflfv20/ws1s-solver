package ch.epfl.fv20.ws1s

import Language._
import Kernel._

/*
Transform a top level formula into an (hopefully) equisatisfiable formula in the kernel. If everything goes as planned, without exponential blowup.
 */
object Translator {
  var increment: Int = 0
  def next():String = {
    increment+=1
    "x"+increment
  }

  case class Context(m1: Map[Variable1, Value1], m2: Map[Variable2, Value2], mb:Map[VariableB, Boolean])
  type Mapping = Map[Language.Variable, Kernel.Variable]


  def instantiateAll(b:Boolean, c:Context):Boolean =  c.mb.foldLeft(b)( (s, p) => b.instantiateBooleanVariable(p._1, p._2) )

  def translate(b: Boolean, c:Context, mapping: Mapping): (Formula, Context, Mapping) ={
    return ???/*
    val b1 = instantiateAll(b, c)
    b match {
      case Language.T => (Kernel.tr, c, mapping)
      case Language.F => (~Kernel.tr, c, mapping)
      case VariableB(name) => ~Kernel.tr   //should not happen for now since all boolean variables should get instantiated. Boolean Variables could be implemented though.
      case Equal1(l, r) =>{
        val f1 = translate(l, c, mapping)
        val l1 = Kernel.Variable()
        val l2 = Kernel.Variable
      }
      case Succ1(l, r) =>
      case Equal2(l, r) =>
      case Succ2(l, r) =>
      case Subset(l, r) =>
      case And(l, r) =>
      case Or(l, r) =>
      case Not(b) =>
      case Exists(v, b) =>
      case Forall(v, b) =>
    }*/
  }

  /*
  From some value of first order, return a variable and a formula asserting that the variable is the value it is supposed to be.
  Context is probably useless here, but need to see once implementing translation of booleans.
  Mapping probably needs to be carried away and entries deleted when encountering an existential quantifier. Need to see as well.
   */
  def formulaFromValue(x:Value1, c:Context, mapping:Mapping): (Kernel.Variable, Formula, Context, Mapping) = {
    x match {
      case Variable1(name) => {
        if (mapping.contains(Variable1(name))) (mapping(Variable1(name)), singleton(mapping(Variable1(name))), c, mapping )
        else {
          val y = Kernel.Variable(next())
          (y, singleton(y), c, mapping + ((Variable1(name), y)))
        }
      }
      case Successor(v) => {
        val (va, f, c1, m) = formulaFromValue(v, c, mapping)
        val y = Kernel.Variable(next())
        (y, succ(va, y)/\f, c1, m )
      }
      case Constant1(0) => {
        val y = Variable("z0")
        (y, tr, c, mapping)
      }
      case Constant1(n) => {
        val y = Variable("z"+n)
        (y, tr, c, mapping)
      }
      case Plus_n(v, n) => {
        n match {
          case Constant1(0) =>formulaFromValue(v, c, mapping)
          case Constant1(m) =>{
            val (va, f, c1, ma) = formulaFromValue(Plus_n(v, Constant1(m-1)), c, mapping)
            val y = Kernel.Variable(next())
            (y, succ(va, y)/\f, c1, ma )

          }
        }
      }
    }
  }
  def formulaFromValue(X:Value2, c:Context, mapping:Mapping): (Formula, Context, Mapping) = {
???
  }
}
