package ch.epfl.fv20.ws1s

object Kernel {

  abstract sealed class Formula() {
    def freeVariables: Set[Variable] = this match {
      case subset(l, r) => Set(l, r)
      case succ(l, r) => Set(l, r)
      case or(l, r) => l.freeVariables ++ r.freeVariables
      case and(l, r) => l.freeVariables ++ r.freeVariables
      case not(f) => f.freeVariables
      case exists(v, f) => f.freeVariables - v
      case tr => Set()
    }

    def unary_~ = not(this)

    def \/(that: Formula) = orS(this, that)

    def /\(that: Formula) = andS(this, that)

    def ==>(that:Formula) : Formula = implies(this, that)

  }

  case class Variable(name: String){
    def ===(that: Variable): Formula = equal(this, that)

  }
  val ? = exists

  case class subset(l: Variable, r: Variable) extends Formula
  case class equal(l: Variable, r: Variable) extends Formula

  case class succ(l: Variable, r: Variable) extends Formula //succ for first order variables lifted to sets. NOT FOR ARITHMETIC!
  case class singleton(v: Variable) extends Formula
  case class is_empty(v: Variable) extends Formula
  case class zeroth(v: Variable) extends Formula

  case class or(l: Formula, r: Formula) extends Formula
  case class and(l: Formula, r: Formula) extends Formula
  case class iff(l: Formula, r: Formula) extends Formula

  case class not(f: Formula) extends Formula

  case class exists(v: Variable, f: Formula) extends Formula
  case object tr extends Formula


  //Macros and shortcuts
  def andS(l: Formula, r: Formula): Formula = (l, r) match {
    case (`tr`, r) => r
    case (l, `tr`) => l
    case (l, r) => and(l, r)
  }

  def orS(l: Formula, r: Formula): Formula = (l, r) match {
    case (`tr`, r) => r
    case (l, `tr`) => l
    case (l, r) => or(l, r)
  }
  def implies(l:Formula, r:Formula): Formula = ~l \/ r

  def forall(v: Variable, f: Formula): Formula = ~ ?(v, ~f)

  def A(v: Variable, f: Formula): Formula = forall(v, f)



  //Many other shorcuts and syntactic sugar to be defined

}
