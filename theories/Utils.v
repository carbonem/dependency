From mathcomp Require Import all_ssreflect zify.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Locate Forall.

Notation In := List.In.
Notation Forall := List.Forall.


Lemma In_in : forall (A : eqType) (a : A) l, In a l <-> a \in l.
Proof.
move => A a. elim. split;done.
intros. rewrite /= inE. split. case. move=>->. rewrite eqxx. done. move/H. move=>->. by rewrite orbC. 
move/orP. case. move/eqP. move=>->. auto. move/H. auto. 
Qed.

Lemma Forall_forall
     : forall (A : eqType) (P : A -> Prop) (l : seq A), Forall P l <-> (forall x : A, x \in l -> P x).
Proof. intros. rewrite List.Forall_forall. split;intros;auto;by apply/H/In_in. Qed.

Lemma nat_fact : forall n, n - (n - n) = n. lia. Qed.

Lemma forallzipP1 : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) -> 
Forall P (zip l l').
Proof.
intros. apply/Forall_forall. intros. move : H1. move/nthP=>HH. specialize HH with (a,b). 
destruct HH. rewrite -H2. rewrite nth_zip //=. apply H0. move : H1. by rewrite size_zip minnE H nat_fact. 
Qed.


Lemma forallzipP2 : forall (A B : eqType) (P : A * B -> Prop) a b l l', Forall P (zip l l') -> size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)).
Proof.
move => A B P a b. elim. case. done. done. move => a0 l IH. case. done. move => a1 l0 H Hsize. intros. simpl in H0. destruct x0. simpl. simpl in H. inversion H. done. simpl. apply IH. simpl in H. inversion H. done. simpl in Hsize. lia. lia. 
Qed.

Lemma forallzipP : forall (A B : eqType) (P : A * B -> Prop) a b l l',  size l = size l' -> (forall x0, x0 < size l -> P (nth a l x0,nth b l' x0)) <-> 
Forall P (zip l l').
Proof.
intros.  split. apply forallzipP1. done. move/forallzipP2=>HH. apply HH. done. 
Qed.

Lemma forallP : forall (A : eqType) (P : A -> Prop) a l,(forall x0, x0 < size l -> P (nth a l x0)) -> 
Forall P l.
Proof. intros.
apply/Forall_forall. intros. move : H0 => /nthP H3.  specialize H3 with a. destruct H3. rewrite -H1. auto.
Qed.

Lemma my_in_cons : forall (A :eqType) (a : A) l, a \in (a::l).
Proof. intros. rewrite !inE eqxx. done. Qed.

Lemma my_in_cons2 : forall (A :eqType) (a a0 : A) l, a \in l -> a \in (a0::l).
Proof. intros. rewrite !inE H. lia. Qed.

Hint Resolve my_in_cons my_in_cons2.

Ltac case_if := match goal with 
                | [ |- context[if ?X then _ else _ ]] => have : X by subst
                | [ |- context[if ?X then _ else _ ]] => have : X = false by subst 

                | [ |- context[if ?X then _ else _ ]] => let H := fresh in destruct X eqn:H

                end; try (move=>->).

(*Ltac iflia := case_if;*)

Ltac rifliad := (repeat case_if); try done.
