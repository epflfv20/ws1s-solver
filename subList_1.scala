import stainless.collection._
import stainless.lang._
import stainless.annotation._
 
object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  def subListRefl[T](@induct l: List[T]): Unit = {
  }.ensuring(_ =>
    subList(l, l)
  )
  
  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))
    subListRefl(l1.tail)
    subListTrans(l1.tail, l1, l2)
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )
 
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    assert(subList(l1.tail, l2.tail) || subList(l1, l2.tail))
    if(subList(l1, l2.tail)) {
      subListTail(l1, l2.tail)
    }
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )
 
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))
    (l1, l2, l3) match {
      case (Nil(), Nil(), Nil()) => ()
      case _ => (l1, l3) match {
        case (Nil(), _) => ()
        case (Cons(x, xs), Cons(y, ys)) => {
          if(x == l2.head && subList(xs, l2.tail)) {
            if(l2.head == y && subList(l2.tail, ys)){
              subListTrans(xs, l2.tail, ys)
            }
            else {
              subListTrans(l1, l2, ys)
            }
          }
          else {
            if(l2.head == y && subList(l2.tail, ys)){
              subListTrans(l1, l2.tail, ys)
            }
            else {
              subListTrans(l1, l2, ys)
            }
          }
        }
      }
    }
  }.ensuring(_ =>
    subList(l1, l3)
  )
 
  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(x, xs), Cons(y, ys)) => {
        if(x == y && subList(xs, ys)) {
          subListLength(xs, ys)
        }
        else {
          subListLength(l1, ys)
        }
      }
    }
  }.ensuring(_ =>
    l1.length <= l2.length
  )
 
  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)
    subListLength(l1, l2)
    (l1, l2) match {
      case (Nil(), Nil()) => ()
      case (Cons(x, xs), Cons(y, ys)) => subListEqual(xs, ys)
    }
  }.ensuring(_ =>
    l1 == l2
  )
 
  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))
    subListLength(l2, l1)
    subListEqual(l1, l2)
  }.ensuring(_ =>
    l1 == l2
  )
 
  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }
 
}