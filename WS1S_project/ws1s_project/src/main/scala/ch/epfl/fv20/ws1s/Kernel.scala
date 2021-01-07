package ch.epfl.fv20.ws1s

object Kernel {

  abstract sealed class Formula() {
    def freeVariables: Set[Variable] = this match {
      case subset(l, r) => Set(l, r)
      case succ(l, r) => Set(l, r)
      case or(l, r) => l.freeVariables ++ r.freeVariables
      case not(f) => f.freeVariables
      case exists(v, f) => f.freeVariables - v
      case tr => Set()
    }

    def unary_~ = not(this)

    def \/(that: Formula) = or(this, that)

    def /\(that: Formula) = and(this, that)

    def ==>(that:Formula) : Formula = implies(this, that)

  }

  case class Variable(name: String){
    def ===(that: Variable): Formula = equ(this, that)

  }
  val ? = exists

  case class subset(l: Variable, r: Variable) extends Formula

  case class succ(l: Variable, r: Variable) extends Formula //succ for first order variables lifted to sets. NOT FOR ARITHMETIC!

  case class or(l: Formula, r: Formula) extends Formula

  case class not(f: Formula) extends Formula

  case class exists(v: Variable, f: Formula) extends Formula
  case object tr extends Formula





  //Macros and shortcuts

  def and(l: Formula, r: Formula): Formula = ~((~l) \/ (~r))
  def implies(l:Formula, r:Formula): Formula = ~l \/ r
  def iff(l:Formula, r:Formula): Formula = and(implies(l, r), implies (r, l))


  def forall(v: Variable, f: Formula): Formula = ~ ?(v, ~f)

  def A(v: Variable, f: Formula): Formula = forall(v, f)

  // def equ(x: Variable, y: Variable): Formula = subset(x, y) /\ subset(y, x)
  def equ(x: Variable, y: Variable): Formula = subset(x, y) /\ subset(y, x)
  def is_empty(x:Variable): Formula = {
    val y = Variable(x.name+"'")
    A(y, subset(x, y))

  }
  def singleton(x:Variable) : Formula = {
    val y = Variable(x.name+"'")
//    ~or(is_empty(x), exists(y, subset(y, x)  /\ (~is_empty(y) \/ ~subset(x, y))))
    and(not(is_empty(x)), forall(y, implies(and(subset(y, x), not(subset(x, y))), is_empty((y)))))
  }


  def zeroth(x:Variable) : Formula = {
    val y = Variable(x.name+"'")
    singleton(x) /\ A(y, ~succ(y, x))
  }
  def first(x:Variable) : Formula = {
    val y = Variable(x.name+"'")
    exists(y, succ(y, x) /\ zeroth(y))
  }


  //Many other shorcuts and syntactic sugar to be defined

}
