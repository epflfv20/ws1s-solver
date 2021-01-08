package ch.epfl.fv20.ws1s

import Language._
import Kernel._
import Solver.solve
/*
Transform a top level formula into an (hopefully) equisatisfiable formula in the kernel. If everything goes as planned, without exponential blowup.
 */
object Interpreter {
  var increment: Int = 0
  def next():String = { //names for skolemization
    increment+=1
    "x"+increment
  }
  def next2():String = { //names for any variables user-defined
    increment+=1
    "y"+increment
  }
  def next3():String = { //names for variables defined in context
    increment+=1
    "w"+increment
  }
  def translateAndSolve(b:BooleanFormula, c:Context=emptyc): Option[Map[Language.Variable, String]] = {
    val (f1, m) = translateComplete(b, c)
    val r= solve(f1)
    r match {
      case Some(m2) => Some(m.map( e => e._1 match {
        case Variable1(name) => (e._1, m2(e._2).zipWithIndex.filter(_._1 == '1').map(_._2).toSet.head.toString)
        case Variable2(name) => (e._1, m2(e._2).zipWithIndex.filter(_._1 == '1').map(_._2).toSet.toString())
      } ))
      case None => None
    }

  }
  // variables denotic first order integers start with z.

  case class Context(m1: Map[Variable1, Value1], m2: Map[Variable2, Value2], mb:Map[VariableB, BooleanFormula])
  type Mapping = Map[Language.Variable, Kernel.Variable]
  val emptyc = Context(Map.empty[Variable1, Value1], Map.empty[Variable2, Value2], Map.empty[VariableB, BooleanFormula])
  val emptym : Mapping = Map.empty[Language.Variable, Kernel.Variable]


  def instantiateAll(b:BooleanFormula, c:Context):BooleanFormula =  c.mb.foldLeft(b)((s, p) => b.instantiateBooleanVariable(p._1, p._2) )

  def translateComplete(b:BooleanFormula, c:Context): (Formula, Mapping) = {
    //get the formula for the desired BooleanFormula

    //get Formulas for values defined in context, while keeping trace of the mapping. Only the Mapping is cumulative, other are not.
    val temp1:List[ (Kernel.Variable, Formula, Mapping)] = c.m1.toList.scanLeft[(Kernel.Variable, Formula, Mapping), List[ (Kernel.Variable, Formula, Mapping)]](
      (Variable(""), tr, emptym))(op= (previous, current)  => {
      val x = Variable(next3())
      formulaFromValue(current._2, previous._3+((current._1, x)), Some(x)) //instead of defining the value with a new variable, directly use the defined variable to spare en exists()
    } )
    val temp2:List[(Kernel.Variable, Formula, Mapping)] = c.m2.toList.scanLeft[(Kernel.Variable, Formula, Mapping), List[(Kernel.Variable, Formula, Mapping)]](
      (Variable(""), tr, temp1.last._3))(op= (previous, current)  => {
      val x = Variable(next3())
      formulaFromValue(current._2, previous._3+((current._1, x)), Some(x)) //instead of defining the value with a new variable, directly use the defined variable to spare en exists()
    } )
    val sub = translate(b, c, temp2.last._3 )
    //conjunctions of definitions of first order and second order variables in context
    val fin: Formula = temp1.map(f => f._2).reduce((i, j) => i /\ j) /\ temp2.map(f => f._2).reduce((i, j) => i /\ j) /\ sub._1
    val main: Formula = b.freeVariables.foldLeft[Kernel.Formula](fin)((f:Formula, v:Language.Variable) => v match {
      case Variable1(name) => {
        singleton(sub._2(v)) /\ f
      }
      case Variable2(name) => f
    })
    val ints = main.freeVariables.filter(_.name(0)=='z').map(_.name.substring(1).toInt)
    val main2 = if (ints.nonEmpty) (0 to ints.max).foldLeft(main)((f:Formula, n:Int) => {
      if (n == 0) zeroth(Variable("z0"))/\ f else succ(Variable("z"+(n-1)), Variable("z"+n)) /\ f
    }) else main
    (main2, sub._2)

  }
  def translate(b: BooleanFormula, c:Context, mapping: Mapping): (Formula, Mapping) ={

    val b1 = instantiateAll(b, c)
    b match {
      case Language.T => (Kernel.tr, mapping)
      case Language.F => (~Kernel.tr, mapping)
      case v:VariableB => translate(c.mb(v), c, mapping) //For when a variable has been defined in context. For now, boolean variables aren't real and can't be quantified over, though it could be otherwise.
      case Equal1(l, r) =>{
        val l1 = formulaFromValue(l, mapping, None)
        val r1 = formulaFromValue(r, l1._3, None)
        val form =  l1._2 /\ r1._2 /\ equal(l1._1, r1._1)
        val form1 = if (l1._2 == tr) form else exists(l1._1, form)
        val form2 = if (r1._2 == tr) form1 else exists(r1._1, form1)
        (form2, r1._3)
      }
      case Succ1(l, r) => {
        val l1 = formulaFromValue(l, mapping, None)
        val r1 = formulaFromValue(r, l1._3, None)
        val form = l1._2 /\ r1._2 /\ succ(l1._1, r1._1)
        val form1 = if (l1._2 == tr) form else exists(l1._1, form)
        val form2 = if (r1._2 == tr) form1 else exists(r1._1, form1)
        (form2, r1._3)
      }

      case In(l, r) => {
        val l1 = formulaFromValue(l, mapping, None)
        val r1 = formulaFromValue(r, l1._3)
        val form = l1._2 /\ r1._2 /\ subset(l1._1, r1._1)
        val form1 = if (l1._2 == tr) form else exists(l1._1, form)
        val form2 = if (r1._2 == tr) form1 else exists(r1._1, form1)
        (form2, r1._3)

      }
      case Equal2(l, r) =>{
        val l1 = formulaFromValue(l, mapping)
        val r1 = formulaFromValue(r, l1._3)
        val form = l1._2 /\ r1._2 /\ equal(l1._1, r1._1)
        val form1 = if (l1._2 == tr) form else exists(l1._1, form)
        val form2 = if (r1._2 == tr) form1 else exists(r1._1, form1)
        (form2, r1._3)
      }
      case Succ2(l, r) => {
        val C = Kernel.Variable(next())
        val p = Kernel.Variable(next())
        val p1 = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        val A = t1._1
        val B = Variable("z1")
        val mod2 = iff(iff( subset(p, A), subset(p, B) ), iff( subset(p, C), subset(p, t2._1) ))
        val atleast2 = ?(p1, succ(p, p1) /\ iff(subset(p1, C), ( (subset(p, A) /\ subset(p, B)) \/ (subset(p, A) /\ subset(p, C) \/ (subset(p, B) /\ subset(p, C))) )))
        val cond = exists(C, ~subset(Variable("z0"), C) /\ forall( p, implies(singleton(p), mod2 /\ atleast2) ))
        val form = t1._2 /\ t2._2 /\ cond
        val form1 = if (t1._2 == tr) form else exists(t1._1, form)
        val form2 = if (t2._2 == tr) form1 else exists(t2._1, form1)
        (form2 , t2._3)
      }
      case Subset(l, r) =>{
        val l1 = formulaFromValue(l, mapping)
        val r1 = formulaFromValue(r, l1._3)

        val form = l1._2 /\ r1._2 /\ subset(l1._1, r1._1)
        val form1 = if (l1._2 == tr) form else exists(l1._1, form)
        val form2 = if (r1._2 == tr) form1 else exists(r1._1, form1)
        (form2, r1._3)
      }
      case And(l, r) => {
        val l1 = translate(l, c, mapping)
        val r1 = translate(r, c, l1._2)
        (and(l1._1, r1._1) , r1._2)
      }

      case Or(l, r) => {
        val l1 = translate(l, c, mapping)
        val r1 = translate(r, c, l1._2)
        (or(l1._1, r1._1) , r1._2)
      }
      case Not(b) =>{
        val b1 = translate(b, c, mapping)
        (not(b1._1) , b1._2)
      }
      case Exists(v, b) =>{
        val (b1, newMap) = if (mapping.contains(v)){
          val currentvMap:Kernel.Variable = mapping(v)
          val b1 = translate(b, c, mapping - v)
          val newMap: Mapping = (b1._2 - v) + ((v, currentvMap))
          (b1, newMap)
        }
        else {
          val b1 = translate(b, c, mapping - v)
          (b1, b1._2-v)
        }
        val form = v match {
          case Variable1(name) => exists(b1._2(v), singleton(b1._2(v)) /\ b1._1 )
          case Variable2(name) =>exists(b1._2(v), b1._1)
        }
        (form, newMap)
      }
      case Forall(v, b) =>{
        val (b1, newMap) = if (mapping.contains(v)){
          val currentvMap:Kernel.Variable = mapping(v)
          val b1 = translate(b, c, mapping - v)
          val newMap: Mapping = (b1._2 - v) + ((v, currentvMap))
          (b1, newMap)
        }
        else {
          val b1 = translate(b, c, mapping)
          (b1, b1._2-v)
        }
        val form = v match {
          case Variable1(name) => forall(b1._2(v), implies(singleton(b1._2(v)), b1._1) )
          case Variable2(name) => forall(b1._2(v), b1._1)
        }
        (form, newMap)
      }
    }
  }

  /*
  From some value of first order, return a variable and a formula asserting that the variable is the value it is supposed to be.
   */
  def formulaFromValue(x:Value1, mapping:Mapping, y1:Option[Kernel.Variable]): (Kernel.Variable, Formula, Mapping) = {
    x match {
      case x:Variable1 => {
        if (mapping.contains(x)) (mapping(x), tr, mapping )
        else {
          val y = Kernel.Variable(next2())
          (y, tr, mapping + ((x, y)))
        }
      }
      case Successor(v) => {
        val (va, f, m) = formulaFromValue(v, mapping, None)
        val y: Kernel.Variable = y1 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
        val form = if (f==tr)  succ(va, y)/\f else exists(va, f /\ succ(va, y))
        (y, form, m )
      }
      case Constant1(n) => {
        y1 match {
          case Some(y) => (y, equal(y, Variable("z"+n)), mapping)
          case None =>(Variable("z"+n), tr, mapping)
        }
      }
      case Plus_n(v, n) => {
        n match {
          case Constant1(0) =>formulaFromValue(v, mapping, None)
          case Constant1(m) =>{
            val (va, f, ma) = formulaFromValue(Plus_n(v, Constant1(m-1)), mapping, None)
            val y: Kernel.Variable = y1 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
            val form = if (f==tr)  f /\ succ(va, y) else exists(va, succ(va, y)/\f)
            (y, form, ma )

          }
        }
      }
    }
  }
  def formulaFromValue(X:Value2,  mapping:Mapping, y2:Option[Kernel.Variable] = None): (Kernel.Variable, Formula, Mapping) = {
    X match {
      case Variable2(name) => {
        if (mapping.contains(Variable2(name))) (mapping(Variable2(name)), tr, mapping )
        else {
          val y = Kernel.Variable(next2())
          (y, tr, mapping + ((Variable2(name), y)))
        }
      }
      case ConstantPredicate(s) =>{
        val y: Kernel.Variable = y2 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
        val q = Kernel.Variable(next())
        val temp : Set[(Kernel.Variable, Formula, Mapping)] =
          s.scanLeft[(Kernel.Variable, Formula, Mapping), Set[(Kernel.Variable, Formula, Mapping)]]((y, tr, mapping))(op = (f:(Kernel.Variable, Formula, Mapping), v:Value1) => formulaFromValue(v, f._3, None))
        val cond: (Formula, Formula, Mapping) = temp.foldLeft[(Formula, Formula, Mapping)](tr, tr, mapping)(op = (f:(Formula, Formula, Mapping), g:(Kernel.Variable, Formula, Mapping)) => {
          (f._1 \/ subset(q,g._1), f._2 /\ g._2, g._3)
        })
        val form : Formula = temp.foldLeft[Formula](cond._2 /\ Kernel.forall(q, implies(singleton(q), iff(subset(q, y), cond._1) )))(
          (f:Formula, t:(Kernel.Variable, Formula, Mapping)) => if (t._2 == tr) f else exists(t._1, f))
        (y, form, mapping )
      }
      case Union(l, r) => {
        val y: Kernel.Variable = y2 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
        val q = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        val form =  t1._2 /\t2._2 /\ Kernel.forall(q, implies(singleton(q), iff(subset(q, y), subset(y, t1._1) \/ subset(y, t2._1) ) ))
        val form1 = if (t1._2 == tr) form else exists(t1._1, form)
        val form2 = if (t2._2 == tr) form1 else exists(t2._1, form1)
        (y, form2, t2._3)
      }

      case Intersection(l, r) =>{
        val y: Kernel.Variable = y2 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
        val q = Kernel.Variable(next())
        val t1 = formulaFromValue(l, mapping)
        val t2 = formulaFromValue(r, t1._3)
        val form = t1._2 /\t2._2 /\ Kernel.forall(q, implies(singleton(q), iff(subset(q, y), subset(y, t1._1) /\ subset(y, t2._1) ) ))
        val form1 = if (t1._2 == tr) form else exists(t1._1, form)
        val form2 = if (t2._2 == tr) form1 else exists(t2._1, form1)
        (y, form2, t2._3)
      }
      case ConstantInteger2(n) =>{
        val y: Kernel.Variable = y2 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
        val q = Kernel.Variable(next())
        val content = n.toBinaryString.reverse.zipWithIndex.filter(_._1 == '1').map(_._2)
        val cond: Formula = content.foldLeft[Formula](tr)(op = (f:Formula, g:Int) => {
          val v = Variable("z"+g)
          f \/ subset(q,v)
        })
        (y, forall(q, iff(subset(q, y), cond)), mapping)
      }
      case Sum(l, r) =>{
        val y: Kernel.Variable = y2 match {case Some(y) =>y; case None =>Kernel.Variable(next())}
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
        val form = t1._2 /\t2._2 /\ cond
        val form1 = if (t1._2 == tr) form else exists(t1._1, form)
        val form2 = if (t2._2 == tr) form1 else exists(t2._1, form1)
        ( C, form2, t2._3)
      }
      case Product(l, n) => ???
    }
  }
}
