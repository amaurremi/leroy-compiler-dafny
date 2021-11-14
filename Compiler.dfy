// A Dafny implementation of Xavier Leroy's compiler-verification Coq exercises,
// which were offered to students of the Deepspec Summer School 2017.
// The exercises can be found in https://github.com/DeepSpec/dsss17/blob/master/compiler/Compiler.v.
// All subsequent comments enclosed in /*...*/ are taken verbatim from the exercises.
// The single-line comments (starting with //) are for my notes.

/* This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. */

include "Definitions.dfy"
include "Lists.dfy"
include "Sequences.dfy"

module Compiler {

  import opened Definitions
  import opened Lists
  import opened Sequences

  /* * 3. IMP programs whose free variables are in [U]. */

  /* We redefine the abstract syntax of IMP to ensure that all
    variables mentioned in the program are taken from [U]. */

  const U': set<id>
  const vx := "X"
  const vy := "Y"
  const U: set<id> := {vx, vy} + U'
  type Uvar = x: id | x in U witness vx

  datatype aexp =
    | ANum(nat)
    | AId (Uvar)        /*r <--- NEW */
    | APlus(aexp, aexp)
    | AMinus(aexp, aexp)
    | AMult(aexp, aexp)

  datatype bexp =
    | BTrue
    | BFalse
    | BEq(aexp, aexp)
    | BLe(aexp, aexp)
    | BNot(bexp)
    | BAnd(bexp, bexp)

  datatype com =
    | CSkip
    | CAss(Uvar, aexp)   /*r <--- NEW */
    | CSeq(com, com)
    | CIf(bexp, com, com)
    | CWhile(bexp, com)

  /* The code for an arithmetic expression [a]
  - executes in sequence (no branches)
  - deposits the value of [a] at the top of the stack
  - preserves the variable state.
  This is the familiar translation to "reverse Polish notation".
  */

  function compile_aexp (a: aexp) : code
  {
    match a
    case ANum(n) => Cons(Iconst(n), Nil)
    case AId(v) => Cons(Ivar(v), Nil)
    case APlus(a1, a2) => append(compile_aexp(a1), append(compile_aexp(a2), Cons(Iadd, Nil)))
    case AMinus(a1, a2) => append(compile_aexp(a1), append(compile_aexp(a2), Cons(Isub, Nil)))
    case AMult(a1, a2) => append(compile_aexp(a1), append(compile_aexp(a2), Cons(Imul, Nil)))
  }

  /* Some examples. */

  method example1()
  {
    var e1 := compile_aexp(APlus(AId(vx), ANum(1)));
    var expected1 := Cons(Ivar(vx), Cons(Iconst(1), Cons(Iadd, Nil)));
    assert e1 == expected1;

    var e2 := compile_aexp(AMult(AId(vy), APlus(AId(vx), ANum(1))));
    var expected2 := Cons(Ivar(vy), Cons(Ivar(vx), Cons(Iconst(1), Cons(Iadd, Cons(Imul, Nil)))));
    assert e2 == expected2;
  }

  function compile_bexp(b: bexp, cond: bool, ofs: nat) : code
  {
    match b
    case BTrue =>
        if cond then Cons(Ibranch_forward(ofs), Nil) else Nil
    case BFalse =>
        if cond then Nil else Cons(Ibranch_forward(ofs), Nil)
    case BEq(a1, a2) =>
        append(compile_aexp(a1), append(compile_aexp(a2), if cond then Cons(Ibeq(ofs), Nil) else Cons(Ibne(ofs), Nil)))
    case BLe(a1, a2) =>
        append(compile_aexp(a1), append(compile_aexp(a2), if cond then Cons(Ible(ofs), Nil) else Cons(Ibgt(ofs), Nil)))
    case BNot(b1) =>
        compile_bexp(b1, !cond, ofs)
    case BAnd(b1, b2) =>
        var c2 := compile_bexp(b2, cond, ofs);
        var c1 := compile_bexp(b1, false, if cond then length(c2) else ofs + length(c2));
        append(c1, c2)
  }

  /* Examples. */

  method example2()
  {
    var e1 := compile_bexp(BEq(AId(vx), ANum(1)), true, 42);
    var expected1 := Cons(Ivar(vx), Cons(Iconst(1), Cons(Ibeq(42), Nil)));
    assert e1 == expected1;

    var e2 := compile_bexp(BAnd(BLe(ANum(1), AId(vx)), BLe(AId(vx), ANum(10))), false, 42);
    var expected2 := Cons(Iconst(1), Cons(Ivar(vx), Cons(Ibgt(45), Cons(Ivar(vx), Cons(Iconst(10), Cons(Ibgt(42), Nil))))));
    assert e2 == expected2;

    var e3 := compile_bexp(BNot(BAnd(BTrue, BFalse)), true, 42);
    var expected3 := Cons(Ibranch_forward(42), Nil);
    assert e3 == expected3;
  }

  /* The code for a command [c]
  - updates the variable state as prescribed by [c]
  - preserves the stack
  - finishes on the next instruction immediately following the generated code.
  Again, see slides for explanations of the generated branch offsets.
  */

  // Remark: notations are a nice thing in Coq
  function compile_com(c: com) : code
  {
    match c
    case CSkip =>
        Nil
    case CAss(id, a) =>
        append(compile_aexp(a), Cons(Isetvar(id), Nil))
    case CSeq(c1, c2) =>
        append(compile_com(c1), compile_com(c2))
    case CIf(b, ifso, ifnot) =>
        var code_ifso := compile_com(ifso);
        var code_ifnot := compile_com(ifnot);
        append(compile_bexp(b, false, length(code_ifso) + 1),
              append(code_ifso,
                      Cons(Ibranch_forward(length(code_ifnot)),
                          code_ifnot)))
    case CWhile(b, body) =>
        var code_body := compile_com(body);
        var code_test := compile_bexp(b, false, length(code_body) + 1);
        append(code_test,
              append(code_body,
                      Cons(Ibranch_backward(length(code_test) + length(code_body) + 1),
                          Nil)))
  }

  /* The code for a program [p] (a command) is similar, but terminates
    cleanly on an [Ihalt] instruction. */

  function compile_program(p: com): code
  {
    append(compile_com(p), Cons(Ihalt, Nil))
  }

  /* Examples of compilation. */

  method example3()
  {
    var e1 := compile_program(CAss(vx, APlus(AId(vx), ANum(1))));
    var expected1 := Cons(Ivar(vx), Cons(Iconst(1), Cons(Iadd, Cons(Isetvar(vx), Cons(Ihalt, Nil)))));
    assert e1 == expected1;

    var e2 := compile_program(CWhile(BTrue, CSkip));
    var expected2 := Cons(Ibranch_backward(1), Cons(Ihalt, Nil));
    assert e2 == expected2;

    var e3 := compile_program(CIf(BEq(AId(vx), ANum(1)), CAss(vx, ANum(0)), CSkip));
    var expected3 := Cons(Ivar(vx), Cons(Iconst(1), Cons(Ibne(3), Cons(Iconst(0), Cons(Isetvar(vx), Cons(Ibranch_forward(0), Cons(Ihalt, Nil)))))));
    assert e3 == expected3; 
  }

  /* 3. Semantic preservation */

  /* Auxiliary results about code sequences. */

  /* To reason about the execution of compiled code, we need to consider
    code sequences [C2] that are at position [pc] in a bigger code
    sequence [C = C1 ++ C2 ++ C3].  The following predicate
    [codeseq_at C pc C2] does just this. */

  least predicate codeseq_at(C: code, pc: nat, C2: code)
  {
    exists C1, C3 :: pc == length(C1) && C == append(C1, append(C2, C3))
  }

  /* We show a number of no-brainer lemmas about [code_at] and [codeseq_at],
    then populate a "hint database" so that Coq can use them automatically. */

  // I'm concerned about the effect this will have on the Dafny proof:
  // the fact that we can't have a hint database.

  lemma code_at_app(i: instruction, c2: code, c1: code, pc: nat)
    requires pc == length(c1)
    ensures code_at(append(c1, Cons(i, c2)), pc) == Some(i)
  {}

  lemma codeseq_at_head(C: code, pc: nat, i: instruction, C': code)
  requires codeseq_at(C, pc, Cons(i, C'))
  ensures code_at(C, pc) == Some(i)
  {
    forall C1, C3
    | pc == length(C1) && C == append(C1, append(Cons(i, C'), C3))
    {
      code_at_app(i, append(C', C3), C1, pc);
    }
  }

  // Another difference with Coq: no type inference; function signatures have to be written in full
  // One more difference: arguments to lemmas have to be passed explicitly

  lemma codeseq_at_tail(C: code, pc: nat, i: instruction, C': code)
  requires codeseq_at(C, pc, Cons(i, C'))
  ensures codeseq_at(C, pc + 1, C')
  {
    forall C1, C3
        | pc == length(C1) && C == append(C1, append(Cons(i, C'), C3))
        ensures codeseq_at(C, pc + 1, C')
    {
      var C1' := append(C1, Cons(i, Nil));
      assert pc + 1 == length(C1');
      assert C == append(C1', append(C', C3));
    }
  }

  // Lemma codeseq_at_tail:
  //   forall C pc i C',
  //   codeseq_at C pc (i :: C') ->
  //   codeseq_at C (pc + 1) C'.
  // Proof.
  //   intros. inversion H. 
  //   change (C1 ++ (i :: C') ++ C3)
  //     with (C1 ++ (i :: nil) ++ C' ++ C3).
  //   rewrite <- app_ass. constructor. rewrite app_length. auto.
  // Qed. 

  // Lemma codeseq_at_app_left:
  //   forall C pc C1 C2,
  //   codeseq_at C pc (C1 ++ C2) ->
  //   codeseq_at C pc C1.
  // Proof.
  //   intros. inversion H. rewrite app_ass. constructor. auto.
  // Qed.

  // Lemma codeseq_at_app_right:
  //   forall C pc C1 C2,
  //   codeseq_at C pc (C1 ++ C2) ->
  //   codeseq_at C (pc + length C1) C2.
  // Proof.
  //   intros. inversion H. rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
  // Qed.

  // Lemma codeseq_at_app_right2:
  //   forall C pc C1 C2 C3,
  //   codeseq_at C pc (C1 ++ C2 ++ C3) ->
  //   codeseq_at C (pc + length C1) C2.
  // Proof.
  //   intros. inversion H. repeat rewrite app_ass. rewrite <- app_ass. constructor. rewrite app_length. auto.
  // Qed.

  // Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left codeseq_at_app_right codeseq_at_app_right2: codeseq.
}