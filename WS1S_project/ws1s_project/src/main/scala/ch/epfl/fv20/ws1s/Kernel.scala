package ch.epfl.fv20.ws1s

object Kernel {

  abstract sealed class Formula() {
    def freeVariables: Set[Variable] = this match {
      case subset(l, r) => l.freeVariables ++ r.freeVariables
      case succ(l, r) => l.freeVariables ++ r.freeVariables
      case or(l, r) => l.freeVariables ++ r.freeVariables
      case not(f) => f.freeVariables
      case exists(v, f) => f.freeVariables -- v.freeVariables
    }

    def unary_~ = not(this)

    def \/(that: Formula) = or(this, that)

    def /\(that: Formula) = and(this, that)

  }

  sealed trait Value {
    def freeVariables: Set[Variable]
  }

  case class Variable(name: String) extends Value {
    def ===(that: Variable): Formula = equ(this, that)

    override def freeVariables: Set[Variable] = Set(this)
  }
  val ? = exists

  case class subset(l: Value, r: Value) extends Formula

  case class succ(l: Value, r: Value) extends Formula

  case class or(l: Formula, r: Formula) extends Formula

  case class not(f: Formula) extends Formula

  case class exists(v: Value, f: Formula) extends Formula


  def and(l: Formula, r: Formula): Formula = ~((~l) \/ (~r))

  def forall(v: Value, f: Formula): Formula = ~ ?(v, ~f)

  def !(v: Value, f: Formula): Formula = forall(v: Value, f: Formula)

  // def equ(x: Variable, y: Variable): Formula = subset(x, y) /\ subset(y, x)
  def equ(x: Value, y: Value): Formula = subset(x, y) /\ subset(y, x)


  //Many other shorcuts and syntactic sugar to be defined

}
