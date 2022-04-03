(*
 Eksperymenty i praca w toku - jeszcze nie nadaje się do czytania
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrint.
From mathcomp Require Import algebra.rat.
From mathcomp Require Import ring.


From mathcomp Require Import  ssralg.



Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Open Scope ring_scope.

  Set  Printing Coercions.
Lemma natint0 (a : nat) (H: a != 0%N) : a%:Z <> 0%:Z.
Proof.
  move :  H =>  /eqP H /eqP.
  rewrite eqz_nat.
  move   /eqP /H.
  exact id.
Qed.


Lemma natrat0 (a : nat) (H: a != 0%N) : a%:Q != 0%:Q.
Proof.
  by rewrite ssrnum.Num.Theory.pnatr_eq0.
Qed.


 Lemma ratadd (a b x y : nat)  : (b != 0)%N -> (y != 0)%N -> (a%:Q / b%:Q) + (x%:Q / y%:Q) = ((a%:Q * y%:Q + x%:Q * b%:Q ) / ( b%:Q * y%:Q)).
Proof.
  move => b0 y0.
  Check GRing.eqr_div.
  rewrite  GRing.addf_div.
  reflexivity.
  by rewrite ssrnum.Num.Theory.pnatr_eq0.
  by rewrite ssrnum.Num.Theory.pnatr_eq0.
Qed.
Locate "[ rat _ // _ ]".
Inductive Pochodzi : rat -> Prop :=
| Pochodzi0 : Pochodzi 0
| Pochodzi1 : Pochodzi 1
| PochodziC : forall a b : rat, Pochodzi a -> Pochodzi b -> Pochodzi  ((a+b) /  2%:Q).

Print Pochodzi.

Definition hip : Prop := forall p, Pochodzi p -> exists a b : nat, p = (a%:Q)/(( (2^b)%N)%:Q).
(* (a + b) / (Posz 2)%:~R = (Posz a0)%:~R / (Posz 2)%:~R ^+ b0 *)
Section XD.
Variable F : fieldType.
Implicit Types x y z a b c d e f g: F.

Lemma xdd x y z : ((x + y) / z)= (x / z) + (y / z).
Proof.  ring. Qed.
Print xdd.

(*
((Posz q1)%:~R / (Posz 2)%:~R ^+ q2 + (Posz w1)%:~R / (Posz 2)%:~R ^+ w2) / (Posz 2)%:~R =
  (Posz (q1 * 2 ^ w2 + w1 * 2 ^ q2))%:~R / (Posz 2)%:~R ^+ (q2 * w2 + 1)
*)

Lemma xddddd a b c d e (nzero : [&& e != 0, d != 0 & b != 0]) :
  ((a / b) + (c / d)) / e = (a / (b*e)) + (c / (d*e)).
Proof.
  field;assumption.
Qed.
Print xddddd.

Lemma xddddd2 a b c d e (nzero : [&& e != 0, d != 0 & b != 0]) :
  ((a / b) + (c / d)) / e = (a * d + c * b) / (b * d * e).
Proof.
  field;assumption.
Qed.

Lemma xddddd3 a b c d e  q w (nzero : [&& e != 0, d != 0 & b != 0]) :
  q = (a *d +c*b) -> w = (b*d*e) ->
  ((a / b) + (c / d)) / e = q / w.
Proof.
  move => -> ->.
apply xddddd2.
assumption.
Qed.          
  
End XD.

Open Scope nat_scope.

Lemma expgt0 (a b : nat): a != 0 -> a^b != 0.
Proof.

move => H.
elim : b.
by simpl.
move => b /eqP Q.
rewrite expnSr.
apply/eqP.

move => Hq.
apply: Q.
move : Hq => /eqP. 
rewrite muln_eq0 .
move => /orP.
case.
by move /eqP ->.
move => Q.
exfalso.
(* Search false (_ == _) (_ != _). *)
by apply (negP H).
Qed.

Close Scope nat_scope.
Lemma xd : hip.
Proof.
  rewrite /hip => p.
  elim.
  exists 0%N; exists 0%N; reflexivity.
  exists 1%N; exists 0%N; reflexivity.
  move => a b Pa Ha Pb Hb.
  case : Ha => q1. case => q2 ->.
  case: Hb => w1. case => w2 ->.
  (* q1/2^q2 + w1/2^w2 =a /2^b *)
  exists (q1 * (2 ^ w2) + w1 * (2 ^ q2))%N.
  exists (q2 + w2 + 1)%N.
  apply xddddd3.
  apply/andP.
  split. by simpl.
  apply/andP.
  split.
  (* Search _ (_ ^ _)%N . *)
  rewrite ssrnum.Num.Theory.pnatr_eq0.
  apply expgt0.
  by simpl.
  rewrite ssrnum.Num.Theory.pnatr_eq0.
  apply expgt0.
  by simpl.

  move => {Pa Pb a b p}.
  (* Tera tylko wywalić te %R i pracować na nat *)
  field.
  (* albo nawet nie trzeba xD *)
  done.
  move => {Pa Pb a b p}.
  (* Search _ (_ ^ (_ + _))%N. *)
  rewrite expnD.
    (* Search _ (_ ^ (_ * _))%N. *)
  rewrite expnD.
  field.
  done.
Qed.

Open Scope nat_scope.
(*
Lemma ddd  a b : ((2 ^ b)== a * 13) -> False.
  Proof.
Admitted.    
  
Close Scope nat_scope.
Lemma nie_mozna_byc_elfem_w_1_13 : ~ Pochodzi (1%N%:Q / 13%N%:Q) .
Proof.
  move => /xd [a] [b] /eqP .

  rewrite (@GRing.eqr_div _  1%N%:Q 13%N%:Q a%:Q (2^b)%N%:Q ).
  rewrite (eqP ddd).
  Search _ ( 1 * _).
  rewrite  GRing.mul1r.
  Search _ (_ ^ _)%N.
  
  move => /eqP.
  elim: a.
  rewrite GRing.mul0r.
move => /eqP.
rewrite ssrnum.Num.Theory.pnatr_eq0.
Check expgt0.
*)