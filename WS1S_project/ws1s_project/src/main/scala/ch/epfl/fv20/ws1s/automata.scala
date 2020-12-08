package ch.epfl.fv20.ws1s
import scala.io.StdIn

object automata {

  type Symbol = String

  case class Automaton[State](states: Set[State], alphabet: Set[Symbol], transitions: Set[(State, Symbol, State)], initial: State, accepting: Set[State]) {
    // Make the structure of an automata, with useful methods like product of two automatas,
    // inverse automatas, check if automata is valid (path search), ...
    // Maybe a library with this exists already

    require(states.contains(initial) && accepting.subsetOf(states)
      && transitions.subsetOf(for {f <- states; l <- alphabet; t <- states} yield (f, l, t)))

    def is_total(): Boolean = (for {f <- states; l <- alphabet} yield (f, l)).subsetOf(transitions.map(x => (x._1, x._2)))

    def is_deterministic(): Boolean = transitions.size == transitions.map(x => (x._1, x._2)).size

    def inverse: Automaton[State] = copy(accepting = states -- accepting)


    //Create the product automaton of two automatons
    def product[State2](that: Automaton[State2]): Automaton[(State, State2)] = {
      require(this.alphabet == that.alphabet)
      val Q: Set[(State, State2)] = for {q1 <- this.states; q2 <- that.states} yield (q1, q2)
      val D: Set[((State, State2), Symbol, (State, State2))] = for {t1 <- this.transitions; t2 <- that.transitions if t2._2 == t1._2} yield ((t1._1, t2._1), t1._2, (t1._3, t2._3))
      val q0: (State, State2) = (this.initial, that.initial)
      val F: Set[(State, State2)] = for {f1 <- this.accepting; f2 <- that.accepting} yield (f1, f2)
      Automaton[(State, State2)](Q, alphabet, D, q0, F)
    }

    def deterministicalize(): Automaton[Set[State]] = {
      var new_states : Set[Set[State]] = Set()
      var new_transitions : Set[(Set[State],Symbol,Set[State])] = Set()
      var todo = List(Set(this.initial))
      while (!todo.isEmpty) {
        val st : Set[State] = todo.head
        println(st)
        todo = todo.tail
        if (!new_states.contains(st)) {
          val new_new_transitions : Set[(Set[State],Symbol,Set[State])] = 
            for {symbol <- this.alphabet} yield (st, symbol, this.transitions.filter(x => st.contains(x._1) && x._2==symbol).map(x => x._3))
          println(new_new_transitions)
        
          new_transitions ++= new_new_transitions
          new_states += st
          todo ++= new_new_transitions.map(x => x._3).toList
        }
      }

      //val new_accepting = new_states.filter(s => s.forall(x => accepting.contains(x)))
      val new_accepting = new_states.filter(s => s.exists(x => accepting.contains(x)))
      Automaton[Set[State]](new_states, this.alphabet, new_transitions, Set(this.initial), new_accepting)
    }

    //--------------------------------//
    //-------Syntactic Sugar----------//
    //--------------------------------//

    // Let one write M1 X M2 to get the automaton product of M1 and M2
    def X[State2](that: Automaton[State2]) = product[State2](that: Automaton[State2])

    // Let one write -M1 for the inverse automaton of M1
    def unary_- = inverse


  }

  def main(args: Array[String]): Unit = {
    val aut = Automaton[Int](Set(1,2),Set("a"),Set((1,"a",2),(1,"a",1)), 1, Set(2))
    println(aut.deterministicalize())
  }

}

