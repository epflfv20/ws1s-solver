import stainless.collection._
import stainless.lang._
import stainless.annotation._
 
object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  def subListRefl[T](l: List[T]): Unit = {
    if (!l.isEmpty) {
        subListRefl(l.tail)
    }
  }.ensuring(_ =>
    subList(l, l)
  )

  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))

    // l1 appears entirely in l2.tail => we can remove l2.head
    if (subList(l1, l2.tail)) { 
        subListTail(l1, l2.tail)
    }
    // Otherwise the head of l2 must be the head of l1 because of sublist definition
    // We can therefore just drop l1.head and l2.head
  }.ensuring(_ =>
    subList(l1.tail, l2)
  )

  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    
    if (subList(l1, l2.tail)) { 
        subListTail(l1, l2.tail)
    }

    // Other case: the head of l2 must be the head of l1 because of sublist definition
    // We can therefore drop both and it proves the property
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )
 
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))

    if (l1.nonEmpty && l2.nonEmpty) {
        if (l1.head == l2.head) {
            // l1.head == l2.head
            // if l2.head == l3.head then we have l1.head == l3.head and can prove for the 3 tails
            // else, we want to pop the head of l3

            // We recall that l1.tail sublist of l2.tail when l1 sublist of l2
            subListTails(l1, l2)
            if (l2.head == l3.head) {
                // We recall that l2.tail sublist of l3.tail when l2 sublist of l3
                // Because we showed that all heads are equals and that sublist is preserved by tail, we can pop all first elements
                subListTails(l2, l3)
                subListTrans(l1.tail, l2.tail, l3.tail)
            } else {
                subListTrans(l1, l2, l3.tail)
            }
        } else {
            // Head(l1) != Head(l2) ==> we want to pop first element in L2
            // This requires showing that l2.tail is still a sublist of l3, and therefore subListTrans(l1, l2, l3) equiv to subListTrans(l1, l2.tail, l3) if l1.head != l2.head
            subListTail(l2, l3)
            subListTrans(l1, l2.tail, l3)
        }
    }

    assert(true) // Fix "Measure missing"
  }.ensuring(_ =>
    subList(l1, l3)
  )
 
 // The rest is from Zhendong Ang's solution
 
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
