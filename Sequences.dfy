// A Dafny implementation of Xavier Leroy's Sequences module,
// which defines helper lemmas for his compiler-verification exercises.
// https://github.com/DeepSpec/dsss17/blob/master/compiler/Sequences.v
// All subsequent comments enclosed in /*...*/ are taken verbatim from the exercises.
// The single-line comments (starting with //) are for my notes.

// To avoid working with higher-order functions, rather than defining a star relation,
// I will follow the example of the NipkovKlein-chapter7.dfy file and define
// a specialized reflexive, transitive closure relation for the transition predicate.

include "Definitions.dfy"
include "Lists.dfy"

module Sequences {

  import opened Definitions
  import opened Lists

  /* Zero, one or several transitions: reflexive, transitive closure of */
  // transition
  least predicate star_transition(C: code, confA: configuration, confC: configuration)
  {
    || confA == confC
    || exists confB :: transition(C, confA, confB) && star_transition(C, confB, confC)
  }

  /* As usual with small-step semantics, we form sequences of machine transitions
    to define the behavior of a code.  We always start with [pc = 0]
    and an empty evaluation stack.  We stop successfully if [pc] points
    to an [Ihalt] instruction and the evaluation stack is empty.
  */
  predicate mach_terminates (C: code, s_init: state, s_fin: state)
  {
    exists pc ::
    && code_at(C, pc) == Some(Ihalt)
    && star_transition(C, (0, Nil, s_init), (pc, Nil, s_fin))
  }

  greatest predicate infseq_transition(C: code, conf: configuration)
  {
    exists conf2 :: transition(C, conf, conf2) && infseq_transition(C, conf2)
  }

  predicate mach_diverges(C: code, s_init: state)
  {
    infseq_transition(C, (0, Nil, s_init))
  }

  predicate irred_transition(C: code, conf: configuration)
  {
    forall conf2 :: !(transition(C, conf, conf2))
  }

  /* A third case can occur: after a finite number of transitions,
    the machine hits a configuration where it cannot make any transition,
    and this state is not a final configuration ([Ihalt] instruction and empty stack).
    In this case, we say that the machine "goes wrong", which is
    a politically-correct way of saying that our program just crashed. */

  predicate mach_goes_wrong(C: code, s_init: state)
  {
    exists pc, stk, s_fin ::
    && star_transition(C, (0, Nil, s_init), (pc, stk, s_fin))
    && irred_transition(C, (pc, stk, s_fin))
    && (code_at(C, pc) != Some(Ihalt) || stk != Nil)
  }

  /* An important property of the virtual machine is that it is deterministic:
    from a given configuration, it can transition to at most one other configuration. */

  lemma machine_deterministic(C: code, conf: configuration, conf1: configuration, conf2: configuration)
    requires transition(C, conf, conf1)
    requires transition(C, conf, conf2)
    ensures  conf1 == conf2
  {}

  /* As a consequence of this determinism, it follows that
    the final state of a terminating program is unique,
    and that a program cannot both terminate and diverge,
    or terminate and go wrong, or diverge and go wrong.
    These results follow from the generic determinism properties */

  lemma stop_irred(C: code, pc: nat, stk: stack, st: state)
    requires code_at(C, pc) == Some(Ihalt)
    ensures irred_transition(C, (pc, stk, st))
  {}

  // TODO do other predicates have to be least here? I might want to experiment with removing the "least" and see what happens

  least lemma finseq_unique(C: code, a: configuration, c: configuration, c': configuration)
    requires star_transition(C, a, c) && irred_transition(C, c)
    requires star_transition(C, a, c') && irred_transition(C, c')
    ensures c == c'
  {
    if a != c && a != c'
    {
      var b :| transition(C, a, b) && star_transition(C, b, c);
      var b' :| transition(C, a, b') && star_transition(C, b', c');
      machine_deterministic(C, a, b, b');
    }
  }

  lemma terminates_unique(C: code, st: state, st1: state, st2: state)
    requires mach_terminates(C, st, st1)
    requires mach_terminates(C, st, st2)
    ensures st1 == st2
  {
    var pc1 :| code_at(C, pc1) == Some(Ihalt) && star_transition(C, (0, Nil, st), (pc1, Nil, st1));
    var pc2 :| code_at(C, pc2) == Some(Ihalt) && star_transition(C, (0, Nil, st), (pc2, Nil, st2));
    finseq_unique(C, (0, Nil, st), (pc1, Nil, st1), (pc2, Nil, st2));
  }

  lemma terminates_goeswrong_exclusive(C: code, st: state, st': state)
    requires mach_terminates(C, st, st')
    ensures !mach_goes_wrong(C, st)
  {
    var pc :| code_at(C, pc) == Some(Ihalt) && star_transition(C, (0, Nil, st), (pc, Nil, st'));
    var conf := (0, Nil, st);
    var conf' := (pc, Nil, st');
    forall stk_stuck, st_stuck, pc_stuck
      | && star_transition(C, (0, Nil, st), (pc_stuck, stk_stuck, st_stuck))
        && irred_transition(C, (pc_stuck, stk_stuck, st_stuck))
      ensures && pc == pc_stuck
              && stk_stuck == Nil
              {
                finseq_unique(C, conf, conf', (pc_stuck, stk_stuck, st_stuck));
              }
  }

  least lemma infseq_star_inv(C: code, a: configuration, c: configuration)
    requires star_transition(C, a, c)
    requires infseq_transition(C, a)
    ensures infseq_transition(C, c)
  {
    if a != c {
      var b :| && transition(C, a, b)
              && star_transition(C, b, c);
      forall b' | transition(C, a, b') ensures b == b' {
        machine_deterministic(C, a, b, b');
      }
    }
  }

  lemma irred_not_infseq(C: code, a: configuration)
  requires irred_transition(C, a)
  ensures !infseq_transition(C, a)
  {}

  lemma infseq_finseq_excl(C: code, a: configuration, c: configuration)
    requires star_transition(C, a, c)
    requires irred_transition(C, c)
    ensures !infseq_transition(C, a)
  {
    if a != c {
      if infseq_transition(C, a) {
        infseq_star_inv(C, a, c);
      }
    }
  }

  lemma terminates_diverges_exclusive(C: code, st: state, st': state)
    requires mach_terminates(C, st, st')
    ensures !mach_diverges(C, st)
  {
    var pc :| code_at(C, pc) == Some(Ihalt) && star_transition(C, (0, Nil, st), (pc, Nil, st'));
    var conf := (0, Nil, st);
    var conf' := (pc, Nil, st');
    infseq_finseq_excl(C, conf, conf');
  }

  lemma goeswrong_diverges_exclusive(C: code, st: state)
    requires mach_goes_wrong(C, st)
    ensures !mach_diverges(C, st)
  {
    var conf := (0, Nil, st);
    var pc, stk, s_fin :|
      && star_transition(C, conf, (pc, stk, s_fin))
      && irred_transition(C, (pc, stk, s_fin))
      && (code_at(C, pc) != Some(Ihalt) || stk != Nil);
    var conf' := (pc, stk, s_fin);
    infseq_finseq_excl(C, conf, conf');
  }
}