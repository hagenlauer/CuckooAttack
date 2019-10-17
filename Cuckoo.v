Require Import Coq.Logic.Classical.

Section Classical_Predicates.

(* Reset Initial *)

Variables A B : Set.

(* These are essentially just functions in Coq *)
Variables P Q : A -> Prop.

(* We can also use Relations between elements of a set or sets. *)
Variable R : A -> B -> Prop.

(* to say that all elements of A have a property P we write *)
Lemma allAhaveP : forall x:A, P x.
Admitted.

Variable PP : Prop.

(* All of A have property PP possibly containing x:A *)
Lemma allAhavePP : forall x:A, PP.
Admitted.

(* Any element of A which has P also has Q, a clever student is also funny :) *)
Lemma allAwPalsoQ : forall x:A, P x -> Q x.
Admitted.

(* If all A have P, all A with P also have Q, then all A have Q. *)
Lemma allAhaveQ : (forall  x:A, P x) -> (forall x:A, P x -> Q x) -> forall x:A, Q x.
Proof.
intros H1 H2.
intro a.
apply H2.
apply H1.
Qed.

Lemma ex_from_forall : (exists x:A, P x) <-> ~ forall x:A, ~ P x.
Proof.
split.
(* proving -> *)
intro ex.
intro H.
destruct ex as [a p].
assert (npa : ~ (P a)).
apply H.
apply npa.
apply p.
(* proving <- *)
intro H.
apply NNPP.
intro nex.
apply H.
intros a p.
apply nex.
exists a.
exact p.
Qed.

End Classical_Predicates.


(* Parno's 2008 HotSec paper *)

Section Parno.

(* we have sets Person, Computers, TPMs *)
Variables P C T : Set.

(* Properties of P's *)
Variables TrustedPerson  : P -> Prop.

(* Properties of C's *)
Variables TrustedC PhysSecure : C -> Prop.

(* Properties of TPMs *)
Variables TrustedT : T -> Prop.

(* Relations of P and C *)
Variables SaysSecure : P -> C -> Prop.

(* Relations of T and C *)
Variables On : T -> C -> Prop.

(* Relations of C and T *)
Variables CompSaysOn : C -> T -> Prop.

(* Relevant axioms of the trusted system are encoded here *)

(* If a trusted person says so, it is so ... *)
Hypothesis rule1 : forall (p:P) (c:C), TrustedPerson p /\ SaysSecure p c -> PhysSecure c.

(* A TPM on an insecure system can't be trusted *)
Hypothesis rule2 : forall (t:T) (c:C), On t c /\ ~PhysSecure c -> ~TrustedT t.

(* A TPM on a secure system is a trusted *)
Hypothesis rule3 : forall (t:T) (c:C), On t c /\ PhysSecure c -> TrustedT t.

(* A computer with a trusted TPM can be trusted *)
Hypothesis rule4 : forall (t:T) (c:C), On t c /\ TrustedT t -> TrustedC c.

(* A computer with an untrusted TPM can't be trusted *)
Hypothesis rule5 : forall (t:T) (c:C), On t c /\ ~TrustedT t -> ~TrustedC c.

(* The TPM indicated by the computer is the computers TPM. *)
Hypothesis rule6 : forall (c:C) (t:T), CompSaysOn c t -> On t c.

(* Now we encode the assumptions we make about the trust establishment *)

Variable alice : P. (* Alice *)
Variable c : C. (* Alice's computer *)
Variable m : C. (* Adversaries machien *)
Variable tpmm : T. (* Adversaries tpmm *)

(* Alice trusts herself *)
Hypothesis ass1 : TrustedPerson alice.
(* Alice says her computer is secure *)
Hypothesis ass2 : SaysSecure alice c.
(* Adversary controls TPMm on M *)
Hypothesis ass3 : On tpmm m.
(* M is not secure *)
Hypothesis ass4 : ~PhysSecure m.
(* Malware causes Alice's computer to say that TPMm is installed *)
Hypothesis ass5 : CompSaysOn c tpmm.


(* computer C is secure *)
Theorem CisSecure : TrustedPerson alice /\ SaysSecure alice c -> PhysSecure c.
Proof.
  apply rule1.
Qed.

(* Provable with all assumptions ... *)
Theorem PhysSecureC : 
  TrustedPerson alice /\ 
  SaysSecure alice c /\ 
  On tpmm m /\ 
  ~PhysSecure m /\ 
  CompSaysOn c tpmm -> TrustedC c.
Proof.
  intro H.
  assert (TrustedPerson alice /\ SaysSecure alice c -> PhysSecure c).
    - intro H0. apply rule1 in H0. exact H0.
    - Abort.

(* TPM is on C *)
Theorem TPMmONc : PhysSecure c /\ CompSaysOn c tpmm -> On tpmm c.
Proof.
  intro H.
  destruct H.
  apply rule6 in H0.
  exact H0.
Qed.

(* This lets us know that tpmm is on c *)
Lemma TonC : CompSaysOn c tpmm -> On tpmm c.
Proof.
  apply rule6.
Qed.

(* tpmm is trusted *)
Lemma TPM_trusted : On tpmm c /\ PhysSecure c -> TrustedT tpmm.
Proof.
  apply rule3.
Qed.

(* C is trusted *)
Lemma C_trusted : On tpmm c /\ TrustedT tpmm -> TrustedC c.
Proof.
  apply rule4.
Qed.

(* TPM can't be trusted *)
Lemma TPM_not_trusted : On tpmm m /\ ~PhysSecure m -> ~TrustedT tpmm.
Proof.
  apply rule2.
Qed.

Lemma C_not_trusted : On tpmm c /\ ~TrustedT tpmm -> ~TrustedC c.
Proof.
  apply rule5.
Qed.

(* C_trusted and C_not_trusted ! *)

End Parno.






