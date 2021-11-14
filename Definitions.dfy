// A Dafny implementation of Xavier Leroy's compiler-verification Coq exercises,
// which were offered to students of the Deepspec Summer School 2017.
// The exercises can be found in https://github.com/DeepSpec/dsss17/blob/master/compiler/Compiler.v.
// All subsequent comments enclosed in /*...*/ are taken verbatim from the exercises.
// The single-line comments (starting with //) are for my notes.

// This module defines the main data types that are used in the compiler.

/* This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. */

include "Lists.dfy"

module Definitions {
  
  import opened Lists

  /* * 1. The virtual machine. */

  /* The machine operates on a code [c] (a fixed list of instructions)
    and three variable components:
  - a program counter, denoting a position in [c]
  - a state assigning integer values to variables
  - an evaluation stack, containing integers.
  */

  /* The instruction set of the machine. */
  type id = string

  datatype instruction =
    | Iconst(nat)
    | Ivar(id)
    | Isetvar(id)
    | Iadd
    | Isub
    | Imul
    | Ibranch_forward(nat)
    | Ibranch_backward(nat)
    | Ibeq(nat)
    | Ibne(nat)
    | Ible(nat)
    | Ibgt(nat)
    | Ihalt

  type code = list<instruction>

  /* [code_at(C, pc) = Some i] if [i] is the instruction at position [pc]
    in the list of instructions [C]. */

  function code_at (C: code, pc: nat) : option<instruction>
  {
    match (C, pc)
    case (Nil, _)         => None
    case (Cons(i, _), 0)  => Some(i)
    case (Cons(_, C'), n) => code_at(C', n - 1)
  }

  type stack = list<nat>

  /* A state maps atoms to natural numbers*/
  type state = map<id, nat>

  /* The semantics of the virtual machine is given in small-step style,
    as a transition relation between machine configuration: triples
    (program counter, evaluation stack, variable state).
    The transition relation is parameterized by the code [c].
    There is one transition rule for each kind of instruction,
    except [Ihalt], which has no transition. */

  type configuration = (nat, stack, state)

  // A difference between defining inductive datatype in Coq and least predicate
  // is that in the inductive case, we're forced to think about the relationships
  // between all arguments, whereas here, we might forget to include a relationship
  // in the conjunction.
  least predicate transition (C: code, conf1: configuration, conf2: configuration)
  {
    var (pc1, stk1, st1) := conf1;
    var (pc2, stk2, st2) := conf2;
    match code_at(C, pc1)
    case Some(Iconst(n)) =>
        && pc2 == pc1 + 1
        && stk2 == Cons(n, stk1)
        && st2 == st1
    case Some(Ivar(x)) =>
        && pc2 == pc1 + 1
        && x in st1 // TODO: this is different from Leroy
        && stk2 == Cons(st1[x], stk1)
        && st2 == st1
    case Some(Isetvar(x)) =>
        exists v ::
        && pc2 == pc1 + 1
        && stk1 == Cons(v, stk2)
        && st2 == st1[x:=v]
    case Some(Iadd) =>
        exists v1, v2, vs ::
        && pc2 == pc1 + 1
        && stk1 == Cons(v2, Cons(v1, vs))
        && stk2 == Cons(v1 + v2, vs)
        && st1 == st2
    case Some(Isub) =>
        exists v1, v2, vs ::
        && pc2 == pc1 + 1
        && stk1 == Cons(v2, Cons(v1, vs))
        && stk2 == Cons(v1 - v2, vs)
        && st1 == st2
    case Some(Imul) =>
        exists v1, v2, vs ::
        && pc2 == pc1 + 1
        && stk1 == Cons(v2, Cons(v1, vs))
        && stk2 == Cons(v1 * v2, vs)
        && st1 == st2
    case Some(Ibranch_forward(ofs)) =>
        && pc2 == pc1 + 1 + ofs
        && stk1 == stk2
        && st1 == st2
    case Some(Ibranch_backward(ofs)) =>
        && pc1 + 1 > ofs
        && pc2 == pc1 + 1 - ofs
        && stk1 == stk2
        && st1 == st2
    case Some(Ibeq(ofs)) =>
        exists v1, v2 ::
        && stk1 == Cons(v2, Cons(v1, stk2))
        && (if v1 == v2 then pc2 == pc1 + 1 - ofs else pc2 == pc1 + 1)
        && st1 == st2
    case Some(Ibne(ofs)) =>
        exists v1, v2 ::
        && stk1 == Cons(v2, Cons(v1, stk2))
        && (if v1 == v2 then pc2 == pc1 + 1 else pc2 == pc1 + 1 + ofs)
        && st1 == st2
    case Some(Ible(ofs)) =>
        exists v1, v2 ::
        && stk1 == Cons(v2, Cons(v1, stk2))
        && (if v1 < v2 then pc2 == pc1 + 1 + ofs else pc2 == pc1 + 1)
        && st1 == st2
    case Some(Ibgt(ofs)) =>
        exists v1, v2 ::
        && stk1 == Cons(v2, Cons(v1, stk2))
        && (if v1 < v2 then pc2 == pc1 + 1 else pc2 == pc1 + 1 + ofs)
        && st1 == st2
    case Some(Ihalt) => false
    case None => false
  }
}