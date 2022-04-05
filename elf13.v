Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import algebra.rat.
From mathcomp Require Import ring.
From mathcomp Require Import ssrint.
From mathcomp Require Import ssralg.
From mathcomp Require Import prime.

Open Scope ring_scope.

Inductive Pochodzi : rat -> Prop :=
| Pochodzi0 : Pochodzi 0
| Pochodzi1 : Pochodzi 1
| PochodziC : forall a b : rat, Pochodzi a -> Pochodzi b -> Pochodzi  ((a+b) /  2%:Q).


Section PrzerzucanieLiczb.
  Variable F : fieldType.
  Implicit Types a b c d e: F.

  Lemma _rozdzielne a b c d e (nzero : [&& e != 0, d != 0 & b != 0]):
    ((a / b) + (c / d)) / e = (a * d + c * b) / (b * d * e).
  Proof.
    field; assumption.
  Qed.

  Lemma _rozdzielne' a b c d e  q w (nzero : [&& e != 0, d != 0 & b != 0]) :
    q = (a *d +c*b) -> w = (b*d*e) ->
    ((a / b) + (c / d)) / e = q / w.
  Proof.
    move => -> ->.
    apply _rozdzielne.
    assumption.
  Qed.          
  
End PrzerzucanieLiczb.

Open Scope nat_scope.
Lemma expNe0 (a b : nat): a != 0 -> a^b != 0.
Proof.
  move => H.
  rewrite -ssrnat.lt0n.
  rewrite ssrnat.expn_gt0.
  apply/orP; left.
  rewrite ssrnat.lt0n.
  assumption.
Qed.
Close Scope nat_scope.

Lemma pochodzi_w_postaci_a_2b p : Pochodzi p -> exists a b : nat, p = (a%:Q)/((2^b)%N%:Q).
Proof.
  elim.
  exists 0%N; exists 0%N; reflexivity.
  exists 1%N; exists 0%N; reflexivity.
  move => a b Pa Ha Pb Hb.
  case: Ha => q1. case => q2 ->.
  case: Hb => w1. case => w2 ->.
  exists (q1 * (2 ^ w2) + w1 * (2 ^ q2))%N.
  exists (q2 + w2 + 1)%N.
  apply _rozdzielne'.
  apply/andP.
  split. by simpl.
  apply/andP.
  split.
  rewrite ssrnum.Num.Theory.pnatr_eq0.
  apply expNe0.
  by simpl.
  rewrite ssrnum.Num.Theory.pnatr_eq0.
  apply expNe0.
  by simpl.
  by field.
  move => {Pa Pb a b p}.
  rewrite !expnD.
  by field.
Qed.

Lemma primes2 b : 13%N \in (primes (2^ b.+1))%N -> False. 
Proof.
  elim: b.
  by simpl.
  move => b H.
  rewrite expnSr.
  rewrite primesM.
  move => /orP; case.
  assumption.
  by simpl.
  rewrite lt0n.
  apply: expNe0.
  by simpl.
  by simpl.
Qed.

Lemma False_false (P : bool) (H : (P -> False)) : (P = false).
Proof. apply/idP. exact H. Qed.

Lemma primes13 a : 13%N \in (primes (a.+1 * 13 ))%N.
Proof.
  rewrite primesM; [apply/orP; right | |]; by simpl.
Qed.

Lemma dwa_b_a13: forall a b , ((2 ^ b) %N == (a * 13%N)%N) -> False.
Proof.
  elim.
  move => b.
  rewrite mul0n.
  move => /eqP.  
  elim: b.
  by cbn.
  move => n H.
  rewrite expnSr.
  move => /eqP.
  rewrite muln_eq0.
  move => /orP; case.
  move => /eqP; assumption.
  by cbn.
  move => a Ha.
  elim.
  by cbn.
  move => b Hb H.
  move: (f_equal (fun x => 13 \in (primes x))%N (eqP H)).
  rewrite (False_false (@primes2 b)).
  rewrite (@introTF _ _ true idP (primes13 a)).
  done.
Qed.

Lemma nie_mozna_byc_elfem_w_1_13: ~ Pochodzi (1%N%:Q / 13%N%:Q) .
Proof.
  move => /pochodzi_w_postaci_a_2b [a] [b] /eqP .
  rewrite (@GRing.eqr_div _  1%N%:Q 13%N%:Q a%:Q (2^b)%N%:Q ).
  rewrite  GRing.mul1r.
  move => /eqP H.
  apply (@dwa_b_a13 a b).
  rewrite -(@ssrnum.Num.Theory.eqr_nat rat_numDomainType).
  rewrite /intmul in H.
  rewrite H.
  apply/eqP. move => {H}.
  ring.
  by simpl.
  apply /eqP.
  move => /eqP.
  rewrite /intmul.
  rewrite -[0]/(0%:R).
  rewrite (@ssrnum.Num.Theory.eqr_nat).
  elim: b.
  by simpl. move => b H.
  rewrite expnSr.
  rewrite muln_eq0.
  move => /orP. case.
  exact H.
  move => /eqP.
  discriminate. (* Dowód kończy się dyskryminowaniem elfów xD *)
Qed.
