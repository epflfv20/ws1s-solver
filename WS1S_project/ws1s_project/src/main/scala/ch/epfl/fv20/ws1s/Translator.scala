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

  case class Context(m1: Map[Variable1, Value1], m2: Map[Variable2, Value2], mb:Map[VariableB, BooleanFormula])
  type Mapping = Map[Language.Variable, Kernel.Variable]


  def instantiateAll(b:BooleanFormula, c:Context):BooleanFormula =  c.mb.foldLeft(b)((s, p) => b.instantiateBooleanVariable(p._1, p._2) )

  def translate(b: BooleanFormula, c:Context, mapping: Mapping): (Formula, Context, Mapping) ={
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
  def formulaFromValue(x:Value1, mapping:Mapping): (Kernel.Variable, Formula, Mapping) = {
    x match {
      case x:Variable1 => {
        if (mapping.contains(x)) (mapping(x), singleton(mapping(x)), mapping )
        else {
          val y = Kernel.Variable(next())
          (y, singleton(y), mapping + ((x, y)))
        }
      }
      case Successor(v) => {
        val (va, f, m) = formulaFromValue(v, mapping)
        val y = Kernel.Variable(next())
        (y, succ(va, y)/\f, m )
      }
      case Constant1(0) => {
        val y = Variable("z0")
        (y, tr, mapping)
      }
      case Constant1(n) => {
        val y = Variable("z"+n)
        (y, tr, mapping)
      }
      case Plus_n(v, n) => {
        n match {
          case Constant1(0) =>formulaFromValue(v, mapping)
          case Constant1(m) =>{
            val (va, f, ma) = formulaFromValue(Plus_n(v, Constant1(m-1)), mapping)
            val y = Kernel.Variable(next())
            (y, succ(va, y)/\f, ma )

          }
        }
      }
    }
  }
  def formulaFromValue(X:Value2,  mapping:Mapping): (Kernel.Variable, Formula, Mapping) = {
    X match {
      case Variable2(name) => {
        if (mapping.contains(Variable2(name))) (mapping(Variable2(name)), singleton(mapping(Variable2(name))), mapping )
        else {
          val y = Kernel.Variable(next())
          (y, tr, mapping + ((Variable2(name), y)))
        }
      }
      case ConstantPredicate(s) =>{
        val y = Kernel.Variable(next())
        val q = Kernel.Variable(next())
        val temp : Set[(Kernel.Variable, Formula, Mapping)] =
          s.scanLeft[(Kernel.Variable, Formula, Mapping), Set[(Kernel.Variable, Formula, Mapping)]](y, tr, mapping)(op = (f:(Kernel.Variable, Formula, Mapping), v:Value1) =>formulaFromValue(v, f._3))
        val cond: (Formula, Formula, Mapping) = temp.foldLeft[(Formula, Formula, Mapping)](tr, tr, mapping)(op = (f:(Formula, Formula, Mapping), g:(Kernel.Variable, Formula, Mapping)) => {
          (if(f._1==tr) subset(q,g._1) else or(f._1, subset(q,g._1)),  if(f._1==tr) g._2 else  f._2 /\ g._2, g._3)
        })
        (y, Kernel.forall(q, implies(singleton(q), cond._1 /\ subset(q, y) )) /\ cond._2, mapping )
      }
      case Union(l, r) => {
        val y = Kernel.Variable(next())
        val q = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        (y, Kernel.forall(q, implies(singleton(q), iff(subset(q, y), subset(y, t1._1) \/ subset(y, t2._1) ) )) /\t1._2 /\t2._2, t2._3)
      }

      case Intersection(l, r) =>{
        val y = Kernel.Variable(next())
        val q = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        (y, Kernel.forall(q, implies(singleton(q), iff(subset(q, y), subset(y, t1._1) /\ subset(y, t2._1) ) )) /\t1._2 /\t2._2, t2._3)
      }
      case ConstantInteger2(n) =>{
        val y = Kernel.Variable(next())
        val q = Kernel.Variable(next())
        val content = n.toBinaryString.reverse.zipWithIndex.filter(_._1 == '1').map(_._2)
        val cond: Formula = content.foldLeft[Formula](tr)(op = (f:Formula, g:Int) => {
          val v = Variable("z"+g)
          if(f==tr) subset(q,v) else or(f, subset(q,v))
        })
        (y, cond, mapping)
      }
      case Sum(l, r) =>{
        val y = Kernel.Variable(next())
        val C = Kernel.Variable(next())
        val p = Kernel.Variable(next())
        val p1 = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        val A = t1._1
        val B = t2._1
        val mod2 = iff(iff( subset(p, A), subset(p, B) ), iff( subset(p, C), subset(p, y) ))
        val atleast2 = ?(p1, succ(p, p1) /\ iff(subset(p1, C), ( (subset(p, A) /\ subset(p, B)) \/ (subset(p, A) /\ subset(p, C) \/ (subset(p, B) /\ subset(p, C))) )))
        val cond = exists(C, ~subset(Variable("z0"), C) /\ forall( p, implies(singleton(p), mod2 /\ atleast2) ))
        ( y, cond /\ t1._2 /\ t2._2, t2._3)
      }
      case Product(l, n) => ???
    }
  }
}
