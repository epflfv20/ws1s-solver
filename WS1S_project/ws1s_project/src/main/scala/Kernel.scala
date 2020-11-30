
object Kernel {
  abstract sealed class Formula(){
    def freeVariables: Set[Variable] = this match {
      case subset(l, r) => Set(l, r)
      case succ(l, r) =>Set(l, r)
      case or(l, r) =>l.freeVariables ++ r.freeVariables
      case not(f) =>f.freeVariables
      case exists(v, f) =>f.freeVariables - v
      case v: Variable => return Set(v)
    }
    def unary_~ = not(this)
    def \/(that:Formula)= or(this, that)
    def /\(that:Formula) = and(this, that)

  }

  sealed case class Variable(name: String) extends Formula {
    def ===(that: Variable):Formula = equ(this, that)
  }

  case class subset(l: Variable, r: Variable) extends Formula
  case class succ(l: Variable, r:Variable) extends Formula
  case class or(l:Formula, r:Formula) extends Formula
  case class not(f:Formula) extends Formula
  case class exists(v:Variable, f:Formula) extends Formula
  val ? = exists
  def and(l:Formula, r:Formula): Formula = ~( (~l) \/ (~r) )
  def forall(v:Variable, f:Formula) : Formula = ~ ?(v, ~f)
  def !(v:Variable, f:Formula):Formula = forall(v:Variable, f:Formula)

  // def equ(x: Variable, y: Variable): Formula = subset(x, y) /\ subset(y, x)
  def equ(x: Variable, y: Variable): Formula = subset(x, y) /\ subset(y, x)


  //Many other shorcuts and syntactic sugar to be defined

}
