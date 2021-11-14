// A Dafny implementation of Xavier Leroy's compiler-verification Coq exercises,
// which were offered to students of the Deepspec Summer School 2017.
// The exercises can be found in https://github.com/DeepSpec/dsss17/blob/master/compiler/Compiler.v.
// All subsequent comments enclosed in /*...*/ are taken verbatim from the exercises.
// The single-line comments (starting with //) are for my notes.

/* This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. */

/* * 1. The virtual machine. */

/* The machine operates on a code [c] (a fixed list of instructions)
  and three variable components:
- a program counter, denoting a position in [c]
- a state assigning integer values to variables
- an evaluation stack, containing integers.
*/

/* The instruction set of the machine. */

datatype option<T> = Some(T) | None
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

type code = seq<instruction>

/* [code_at(C, pc) = Some i] if [i] is the instruction at position [pc]
  in the list of instructions [C]. */

function code_at (C: code, pc: nat) : option<instruction>
{
  if C == [] then None
  else if pc == 0 then Some(C[0])
  else code_at(C[1..], pc - 1)
}

type stack = seq<nat>

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
      && stk2 == [n] + stk1
      && st2 == st1
  case Some(Ivar(x)) =>
      && pc2 == pc1 + 1
      && x in st1 // TODO: this is different from Leroy
      && stk2 == [st1[x]] + stk1
      && st2 == st1
  case Some(Isetvar(x)) =>
      exists v ::
      && pc2 == pc1 + 1
      && stk1 == [v] + stk2
      && st2 == st1[x:=v]
  case Some(Iadd) =>
      exists v1, v2, vs ::
      && pc2 == pc1 + 1
      && stk1 == [v2, v1] + vs
      && stk2 == [v1 + v2] + vs
      && st1 == st2
  case Some(Isub) =>
      exists v1, v2, vs ::
      && pc2 == pc1 + 1
      && stk1 == [v2, v1] + vs
      && stk2 == [v1 - v2] + vs
      && st1 == st2
  case Some(Imul) =>
      exists v1, v2, vs ::
      && pc2 == pc1 + 1
      && stk1 == [v2, v1] + vs
      && stk2 == [v1 * v2] + vs
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
      && stk1 == [v2, v1] + stk2
      && (if v1 == v2 then pc2 == pc1 + 1 - ofs else pc2 == pc1 + 1)
      && st1 == st2
  case Some(Ibne(ofs)) =>
      exists v1, v2 ::
      && stk1 == [v2, v1] + stk2
      && (if v1 == v2 then pc2 == pc1 + 1 else pc2 == pc1 + 1 + ofs)
      && st1 == st2
  case Some(Ible(ofs)) =>
      exists v1, v2 ::
      && stk1 == [v2, v1] + stk2
      && (if v1 < v2 then pc2 == pc1 + 1 + ofs else pc2 == pc1 + 1)
      && st1 == st2
  case Some(Ibgt(ofs)) =>
      exists v1, v2 ::
      && stk1 == [v2, v1] + stk2
      && (if v1 < v2 then pc2 == pc1 + 1 else pc2 == pc1 + 1 + ofs)
      && st1 == st2
  case Some(Ihalt) => false
  case None => false
}

// To avoid working with higher-order functions, rather than defining a star relation,
// I will follow the example of the NipkovKlein-chapter7.dfy file and define
// a specialized reflexive, transitive closure relation for the transition predicate.

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
  && star_transition(C, (0, [], s_init), (pc, [], s_fin))
}

greatest predicate infseq_transition(C: code, conf: configuration)
{
  exists conf2 :: transition(C, conf, conf2) && infseq_transition(C, conf2)
}

predicate mach_diverges(C: code, s_init: state)
{
  infseq_transition(C, (0, [], s_init))
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
  && star_transition(C, (0, [], s_init), (pc, stk, s_fin))
  && irred_transition(C, (pc, stk, s_fin))
  && (code_at(C, pc) != Some(Ihalt) || stk != [])
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
  var pc1 :| code_at(C, pc1) == Some(Ihalt) && star_transition(C, (0, [], st), (pc1, [], st1));
  var pc2 :| code_at(C, pc2) == Some(Ihalt) && star_transition(C, (0, [], st), (pc2, [], st2));
  finseq_unique(C, (0, [], st), (pc1, [], st1), (pc2, [], st2));
}

lemma terminates_goeswrong_exclusive(C: code, st: state, st': state)
  requires mach_terminates(C, st, st')
  ensures !mach_goes_wrong(C, st)
{
  var pc :| code_at(C, pc) == Some(Ihalt) && star_transition(C, (0, [], st), (pc, [], st'));
  var conf := (0, [], st);
  var conf' := (pc, [], st');
  forall stk_stuck, st_stuck, pc_stuck
    | && star_transition(C, (0, [], st), (pc_stuck, stk_stuck, st_stuck))
      && irred_transition(C, (pc_stuck, stk_stuck, st_stuck))
    ensures && pc == pc_stuck
            && stk_stuck == []
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
  var pc :| code_at(C, pc) == Some(Ihalt) && star_transition(C, (0, [], st), (pc, [], st'));
  var conf := (0, [], st);
  var conf' := (pc, [], st');
  infseq_finseq_excl(C, conf, conf');
}

lemma goeswrong_diverges_exclusive(C: code, st: state)
  requires mach_goes_wrong(C, st)
  ensures !mach_diverges(C, st)
{
  var conf := (0, [], st);
  var pc, stk, s_fin :|
    && star_transition(C, conf, (pc, stk, s_fin))
    && irred_transition(C, (pc, stk, s_fin))
    && (code_at(C, pc) != Some(Ihalt) || stk != []);
  var conf' := (pc, stk, s_fin);
  infseq_finseq_excl(C, conf, conf');
}

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
  case ANum(n) => [Iconst(n)]
  case AId(v) => [Ivar(v)]
  case APlus(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Iadd]
  case AMinus(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Isub]
  case AMult(a1, a2) => compile_aexp(a1) + compile_aexp(a2) + [Imul]
}

/* Some examples. */

method example1()
{
  var e1 := compile_aexp(APlus(AId(vx), ANum(1)));
  var expected1 := [Ivar(vx), Iconst(1), Iadd];
  assert e1 == expected1;

  var e2 := compile_aexp(AMult(AId(vy), APlus(AId(vx), ANum(1))));
  var expected2 := [Ivar(vy), Ivar(vx), Iconst(1), Iadd, Imul];
  assert e2 == expected2;
}

function compile_bexp(b: bexp, cond: bool, ofs: nat) : code
{
  match b
  case BTrue =>
      if cond then [Ibranch_forward(ofs)] else []
  case BFalse =>
      if cond then [] else [Ibranch_forward(ofs)]
  case BEq(a1, a2) =>
      compile_aexp(a1) + compile_aexp(a2) + if cond then [Ibeq(ofs)] else [Ibne(ofs)]
  case BLe(a1, a2) =>
      compile_aexp(a1) + compile_aexp(a2) + if cond then [Ible(ofs)] else [Ibgt(ofs)]
  case BNot(b1) =>
      compile_bexp(b1, !cond, ofs)
  case BAnd(b1, b2) =>
      var c2 := compile_bexp(b2, cond, ofs);
      var c1 := compile_bexp(b1, false, if cond then |c2| else ofs + |c2|);
      c1 + c2
}

/* Examples. */

method example2()
{
  var e1 := compile_bexp(BEq(AId(vx), ANum(1)), true, 42);
  var expected1 := [Ivar(vx), Iconst(1), Ibeq(42)];
  assert e1 == expected1;

  var e2 := compile_bexp(BAnd(BLe(ANum(1), AId(vx)), BLe(AId(vx), ANum(10))), false, 42);
  var expected2 := [Iconst(1), Ivar(vx), Ibgt(45), Ivar(vx), Iconst(10), Ibgt(42)];
  assert e2 == expected2;

  var e3 := compile_bexp(BNot(BAnd(BTrue, BFalse)), true, 42);
  var expected3 := [Ibranch_forward(42)];
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
      []
  case CAss(id, a) =>
      compile_aexp(a) + [Isetvar(id)]
  case CSeq(c1, c2) =>
      compile_com(c1) + compile_com(c2)
  case CIf(b, ifso, ifnot) =>
      var code_ifso := compile_com(ifso);
      var code_ifnot := compile_com(ifnot);
      compile_bexp(b, false, |code_ifso| + 1)
      + code_ifso
      + [Ibranch_forward(|code_ifnot|)]
      + code_ifnot
  case CWhile(b, body) =>
      var code_body := compile_com(body);
      var code_test := compile_bexp(b, false, |code_body| + 1);
      code_test
      + code_body
      + [Ibranch_backward(|code_test| + |code_body| + 1)]
}

/* The code for a program [p] (a command) is similar, but terminates
  cleanly on an [Ihalt] instruction. */

function compile_program(p: com): code
{
  compile_com(p) + [Ihalt]
}

/* Examples of compilation. */

method example3()
{
  var e1 := compile_program(CAss(vx, APlus(AId(vx), ANum(1))));
  var expected1 := [Ivar(vx), Iconst(1), Iadd, Isetvar(vx), Ihalt];
  assert e1 == expected1;

  var e2 := compile_program(CWhile(BTrue, CSkip));
  var expected2 := [Ibranch_backward(1), Ihalt];
  assert e2 == expected2;

  var e3 := compile_program(CIf(BEq(AId(vx), ANum(1)), CAss(vx, ANum(0)), CSkip));
  var expected3 := [Ivar(vx), Iconst(1), Ibne(3), Iconst(0), Isetvar(vx), Ibranch_forward(0), Ihalt];
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
  exists C1, C3 :: pc == |C1| && C == C1 + C2 + C3
}

/* We show a number of no-brainer lemmas about [code_at] and [codeseq_at],
  then populate a "hint database" so that Coq can use them automatically. */

// I'm concerned about the effect this will have on the Dafny proof:
// the fact that we can't have a hint database.

lemma code_at_app(i: instruction, c2: code, c1: code, pc: nat)
  requires pc == |c1|
  ensures code_at(c1 + [i] + c2, pc) == Some(i)
{}

lemma codeseq_at_head(C: code, pc: nat, i: instruction, C': code)
requires codeseq_at(C, pc, [i] + C')
ensures code_at(C, pc) == Some(i)
{
  forall C1, C3
  | pc == |C1| && C == C1 + [i] + C' + C3
  {
    code_at_app(i, C' + C3, C1, pc);
  }
}

// Another difference with Coq: no type inference; function signatures have to be written in full
// One more difference: arguments to lemmas have to be passed explicitly

lemma codeseq_at_tail(C: code, pc: nat, i: instruction, C': code)
requires codeseq_at(C, pc, [i] + C')
ensures codeseq_at(C, pc + 1, C')
{
  forall C1, C3
      | pc == |C1| && C == C1 + [i] + C' + C3
      ensures codeseq_at(C, pc + 1, C')
  {
    var C1' := C1 + [i];
    assert pc + 1 == |C1'|;
    assert C == C1' + C' + C3;
  }
}

// Lemma codeseq_at_tail:
//   forall C pc i C',
//   codeseq_at C pc (i :: C') ->
//   codeseq_at C (pc + 1) C'.
// Proof.
//   intros. inversion H. 
//   change (C1 ++ (i :: C') ++ C3)
//     with (C1 ++ (i :: []) ++ C' ++ C3).
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