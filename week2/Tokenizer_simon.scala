import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.proof.check

object Tokenizer {

  // @extern // WARNING: @extern is unsound, only use for debugging
  // def assume(b: Boolean): Unit = {
  //   (??? : Unit)
  // }.ensuring(_ => b)


  /************************************************************************************************/
  /* Part 1: Parser                                                                               */
  /************************************************************************************************/

  case class Parser[A](parse: List[Token] => Option[(A, List[Token])]) {

    def flatMap[B](f: A => Parser[B]): Parser[B] = Parser(ts => parse(ts).flatMap {
      case (x, rs) => f(x).parse(rs)
    })
  }

  def pure[A](x: A): Parser[A] = Parser((ts: List[Token]) => Some((x, ts)))

  def leftIdentity[A, B](a: A, f: A => Parser[B], ts: List[Token]): Unit = {
    ()
  }.ensuring(_ =>
    pure(a).flatMap(f).parse(ts) == f(a).parse(ts)
  )

  def rightIdentity[A, B](Ma: Parser[A], ts: List[Token]): Unit = {
    ()
  }.ensuring(_ =>
    Ma.flatMap(pure).parse(ts) == Ma.parse(ts)
  )

  def associativity[A, B, C](Ma:Parser[A], f: A => Parser[B], g: B => Parser[C], ts:List[Token]): Unit ={
    ()
  }.ensuring(_ =>
    Ma.flatMap(f).flatMap(g).parse(ts) == Ma.flatMap(x => f(x).flatMap(g)).parse(ts)
  )




  // Following the model of `leftIdentity`, add here the monad laws `rightIdentity` and
  // `associativity` and make sure that Stainless accepts them.


  /************************************************************************************************/
  /* Part 2: Tokenizer                                                                            */
  /************************************************************************************************/

  sealed abstract class Token {
    def chars: List[Char]
  }

  case class Identifier(cs: List[Char]) extends Token {
    override def chars = cs
  }

  case object Open extends Token {
    override def chars = List('(')
  }

  case object Close extends Token {
    override def chars = List(')')
  }

  def isLowerCase(c: Char): Boolean = 'a' <= c && c <= 'z'

  def parsableCharacter(c: Char): Boolean = c == ' ' || c == '(' || c == ')' || isLowerCase(c)

  def parsableToken(t: Token): Boolean = t match {
    case Identifier(cs) => cs.forall(isLowerCase) && !cs.isEmpty
    case _ => true
  }

  @opaque
  def dropWhileForall[T](@induct l: List[T], p1: T => Boolean, p2: T => Boolean): Unit = {
    require(l.forall(p1))
    ()
  }.ensuring(_ => l.dropWhile(p2).forall(p1))

  def tokenize(cs: List[Char]): List[Token] = {
    require(cs.forall(parsableCharacter))
    decreases(cs.length)

    cs match {
      case Nil() => Nil()
      case Cons(c, cs) if c == ' ' => tokenize(cs)
      case Cons(c, cs) if c == '(' => Open :: tokenize(cs)
      case Cons(c, cs) if c == ')'  => Close :: tokenize(cs)
      case Cons(c, cs2) if isLowerCase(c) =>
        val id = cs.takeWhile(isLowerCase)
        val rest = cs.dropWhile(isLowerCase)

        dropWhileForall(cs, parsableCharacter, isLowerCase)

        Identifier(id) :: tokenize(rest)
    }
  }

  // Write and prove the new lemmas you need for questions (4) and (5) here
  @induct
  def forallunion[A](l1: List[A], l2:List[A], p:A=>Boolean): Unit = {
    require(l1.forall(p) && l2.forall(p))
  }.ensuring((l1 ++ l2).forall(p))

  @induct
  def lemmaLowerCase(c:List[Char]):Unit ={
    require(c.forall(isLowerCase))
  }.ensuring(c.forall(parsableCharacter))
  def lemmaTokenChar(t:Token):Unit ={
    require(parsableToken(t))
    t match {
      case Identifier(chars) => {
        assert(chars.forall(isLowerCase))
        lemmaLowerCase(chars)
      }
      case Open => {
        assert(t.chars == List('('))
      }
      case Close => {
        assert(t.chars == List(')'))
      }
    }
  }.ensuring(t.chars.forall(parsableCharacter))

  def lemma1(ts:List[Token]):Unit ={
    require(ts.forall(parsableToken))

    ts match {
      case Nil() => ()
      case Cons(t1, ts2) => {
        assert(ts.flatMap(t => t.chars ++ List(' ')) == t1.chars ++ List(' ') ++ ts2.flatMap(t => t.chars ++ List(' ')))
        assert(parsableToken(t1))
        lemmaTokenChar(t1)
        //assert(ts2.forall(parsableToken))
        lemma1(ts2)
        forallunion(t1.chars, List(' '), parsableCharacter)
        //assert((t1.chars ++ List(' ')).forall(parsableCharacter))
        forallunion(t1.chars ++ List(' '), ts2.flatMap(t => t.chars ++ List(' ')), parsableCharacter)
        //assert((t1.chars ++ List(' ') ++ ts2.flatMap(t => t.chars ++ List(' '))).forall(parsableCharacter))
      }
    }
  }.ensuring(ts.flatMap(t => t.chars ++ List(' ')).forall(parsableCharacter))


  @opaque
  def retokenizeTokens(ts: List[Token]): Unit = {
    require(ts.forall(parsableToken))
    decreases(ts)

    // 4) Add (one or more) calls to lemmas (that will have to state and prove above)
    //    to make sure that the assertion (2) is accepted by Stainless

    // 2) Add an assertion here corresponding to the precondition for the first call to tokenize below

    ts match {
      case Nil() => ()
      case Cons(t, ts2) => {
        lemma1(ts)
        (
          tokenize(ts.flatMap(t => t.chars ++ List(' '))) ==:| trivial |: // by definiton of flatMap

            tokenize((t.chars ++ List(' ')) ++ ts2.flatMap(t => t.chars ++ List(' '))) ==:| trivial |:
            // 5) Complete the equational reasoning here

            ts
          ).qed
      }
    }

  }.ensuring(_ => tokenize(ts.flatMap(t => t.chars ++ List(' '))) == ts)

  @extern
  def main(args: Array[String]) = {

    def scalaListToStainlessList[T](l: scala.collection.immutable.List[T]): List[T] = l match {
      case scala.collection.immutable.Nil => Nil()
      case scala.collection.immutable.::(x, xs) => Cons(x, scalaListToStainlessList(xs))
    }

    def stainlessListToScalaList[T](l: List[T]): scala.collection.immutable.List[T] = l match {
      case Nil()        => scala.collection.immutable.Nil
      case Cons(x, xs)  => scala.collection.immutable.::(x, stainlessListToScalaList(xs))
    }

    val tokens = stainlessListToScalaList(tokenize(scalaListToStainlessList(args(0).toList)))
    println("tokens: " + tokens.mkString(" "))
  }
}