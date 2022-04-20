From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
Require Import Dep.Global_Syntax.


Unset Elimination Schemes. Check seq.
CoInductive sgType  : Type :=
  | SGEnd : sgType  
  | SGMsg : action -> value -> sgType -> sgType  
  | SGBranch : action -> seq sgType -> sgType  .
Set Elimination Schemes.


Inductive Forall2 (A B : Type) (R : A -> B -> Type) : seq A -> seq B -> Prop :=
    Forall2_nil : Forall2 R nil nil | Forall2_cons : forall (x : A) (y : B) (l : seq A) (l' : seq B), R x y -> Forall2 R l l' -> Forall2 R (x :: l) (y :: l').
Hint Constructors Forall2. Search List.Forall.

Inductive Forall3 (A B C : Type) (R : A -> B -> C -> Type) : seq A -> seq B -> seq C -> Prop :=
    Forall3_nil : Forall3 R nil nil nil | Forall3_cons : forall (x : A) (y : B) (z : C) (l : seq A) (l' : seq B) (l'' : seq C), R x y z -> Forall3 R l l' l'' -> Forall3 R (x :: l) (y :: l') (z ::l'').
Hint Constructors Forall3.

Inductive Unravel (r : gType -> sgType -> Prop) : gType -> sgType -> Prop :=
 | UEnd : Unravel r GEnd SGEnd
 | UMsg a u g0 sg0 : Unravel r g0 sg0 -> Unravel r (GMsg a u g0) (SGMsg a u sg0)
 | UBranch gs sgs a : Forall2 (Unravel r) gs sgs ->  Unravel r (GBranch a gs) (SGBranch a sgs)
 | URec g sg : r g[GRec g] sg  -> Unravel r (GRec g) sg.
Hint Constructors Unravel.


Require Import Paco.paco.
Check paco2.

Definition GUnroll g sg : Prop := paco2 Unravel bot2 g sg.

Example test : GUnroll (GRec (GVar 0)) SGEnd.
unfold GUnroll. pcofix CIH. pfold. constructor. right. simpl. done.
Qed.
Check Unravel_ind.
Lemma Unravel_ind2
     : forall r P : gType -> sgType -> Prop,
       P GEnd SGEnd ->
       (forall (a : action) (u : value) (g0 : gType) (sg0 : sgType),
        Unravel r g0 sg0 -> P g0 sg0 -> P (GMsg a u g0) (SGMsg a u sg0)) ->
       (forall (gs : seq gType) (sgs : seq sgType) (a : action),
        Forall2 (Unravel r) gs sgs -> Forall2 P gs sgs -> P (GBranch a gs) (SGBranch a sgs)) ->
       (forall (g : gType) (sg : sgType), r (g)[GRec g] sg -> P (GRec g) sg) ->
       forall (g : gType) (s : sgType), Unravel r g s -> P g s.
Proof.
intros. move : g s H3. fix IH 3. move => g s [].
- apply H.
- intros. apply H0. apply u0.  apply IH. apply u0. 
- intros. apply H1. apply f.
- induction f.  done. constructor. apply IH. apply H3. apply IHf. 
- intros. apply H2. apply r0.
Qed.

Lemma GUnroll_mono : monotone2 Unravel.
Proof.
elim;intros.
-  inversion IN. 
- inversion IN. auto. 
- inversion IN. subst. auto.  
- inversion IN. eauto.  
- inversion IN. subst. constructor. move : l sgs IN H3 H. elim. 
 + intros. inversion H3. auto.
 + intros. inversion H3. subst. constructor. eapply H0.  by  rewrite inE eqxx. eauto. eauto. eauto.
   apply H. constructor. auto. auto.  intros.  eapply H0. by rewrite inE H1 orbC. eauto. eauto. 
Qed.
Hint Resolve GUnroll_mono : paco.

Definition label := (action * (value + nat))%type.
(*Inductive label := 
 | LU : action -> value -> label
 | LN : action -> nat -> label. 

Notation nth_error := List.nth_error.  *)


(*Inductive DAfter : sgType -> label ->  sgType -> Prop :=
 | DMsg a u sg : DAfter (SGMsg a u sg) (LU a u) sg
 | DBranch a g gs i : nth_error gs i = Some g -> DAfter (SGBranch a gs) (LN a i) g.

Inductive After : sgType -> seq label -> sgType -> Prop := 
 | After_0 sg : After sg nil sg
 | After_step a a_s sg0 sg1 sg2 : DAfter sg0 a sg1 -> After sg1 a_s sg2 -> After sg0 (a::a_s) sg2.

Definition act_of_sg sg :=
match sg with 
| SGEnd => None
| SGMsg a _ _ => Some a
| SGBranch a gs => Some a
end.

Definition opt_rel_sg (P : rel action)  (g0 g1 : sgType) :=
if act_of_sg g0 is Some a0
  then if act_of_sg g1 is Some a1
    then P a0 a1
  else false 
else false.*)

Definition same_ch (a0 a1 : action) := action_ch a0 == action_ch a1.

Definition II (a0 a1 : action) := (ptcp_to a0 == ptcp_to a1).
Definition IO (a0 a1 : action) := (ptcp_to a0 == ptcp_from a1).
Definition OO (a0 a1 : action) := (ptcp_from a0 == ptcp_from a1) && same_ch a0 a1.
Definition IO_OO a0 a1 := IO a0 a1 || OO a0 a1.

Inductive InDep : seq action -> Prop :=
 | ID_End a0 a1 : II a0 a1 -> InDep ([::a0; a1])
 | ID_cons a0 a1 aa: IO a0 a1 -> InDep (a1::aa) -> InDep (a0::a1::aa).
Hint Constructors InDep.

(*Fixpoint indep ss := 
match ss with 
| a::s' => match s' with 
         | a'::nil => II a a'
         | a'::s'' => (IO a a') && (indep s')
         | _ => false
         end
| _ => false
end.*)

Definition indep ss := 
match ss with 
| a::a'::ss' => let: one_less := belast a' ss' in path IO a one_less && II (last a one_less) (last a' ss')
| _ => false 
end.

Lemma InDep_iff : forall ss, InDep ss <-> indep ss.
Proof.
case. split;intros;inversion H.
move => a l. case : l. split;intros;inversion H.
move => a0 l. 
elim : l a0 a. rewrite /=. move => a0 a. split;intros; inversion H;subst. done. inversion H4. auto.
move => a0 l H a1. rewrite /=. split;intros.
- inversion H0;subst. rewrite H3 /=. simpl in H. by  apply/H.
- move : H0 => /andP => [] [] /andP => [] []. intros. constructor. done. apply/H. by rewrite /= b b0.
Qed.

Inductive OutDep : seq action -> Prop :=
 | OD_end a0 a1 : IO_OO a0 a1 -> OutDep ([::a0; a1])
 | OD_cons a0 a1 aa: IO_OO a0 a1  -> OutDep (a1::aa) -> OutDep (a0::a1::aa).
Hint Constructors OutDep.

Fixpoint dep (R : action -> action -> bool) ss := 
match ss with 
| nil => false 
| a::s' => match s' with 
          | a'::nil => R a a' 
          | a'::ss' => (R a a') && dep R s'
          | _ => false
        end
        
end.

Definition outdep ss :=
match ss with 
| a::a'::ss => path IO_OO a (a'::ss)
| _ => false 
end. 

Lemma OutDep_iff : forall ss, OutDep ss <-> outdep ss.
Proof.
rewrite /outdep.
case; first (split;intros; inversion H).
move => a []; first (split;intros;inversion H).
move => a0 l. move : l a a0. elim.
- move => a a0. split; rewrite /=;intros. rewrite andbC /=. inversion H; done.
  constructor. by move : H => /andP => [] [].
- move => a l IH a0 a1. split;intros. 
 * inversion H. subst. rewrite /=. simpl in IH. rewrite H2 /=. inversion H4;subst. by rewrite H1. 
   by apply/IH. 
 * simpl in IH,H. move : H=> /andP=> [] []H0 H1. constructor;first done. by apply/IH.  
Qed.
(*Notation outdep := (dep (fun a0 a1 => IO a0 a1 || OO a0 a1)).

Lemma OutDep_iff : forall ss, OutDep ss <-> outdep ss.
Proof.
elim.
- rewrite /=. split;intros;inversion H.
- move => a l H. split;intros. 
 * rewrite /=. case : l H0 H. 
  ** intros. inversion H0. 
  ** intros. case : l H H0. 
   *** intros. inversion H0. apply/orP. done. 
   *** apply/orP.  done. 
 * intros. apply/andP. rewrite -H. inversion H0. split. apply/orP. done. done. 
 
 simpl in H0. case : l H H0. 
 *  done. 
 * move => a0 l H [].
  ** case : l H. 
   *** intros. constructor. by apply/orP.
   *** move => a1 l H /andP. move => [] H2 H3.  constructor.  apply/orP. done. apply/H. done. 
Qed.*)

Ltac contra_list := match goal with 
                      | H : (nil = _ ++ _) |-  _ => apply List.app_cons_not_nil in H
                      end;contradiction.

(*Definition OutDep2 (s : seq action) := exists a a' s', s = a::a'::s' /\ path ((fun a0 a1 => (IO a0 a1) || (OO a0 a1))) a (a'::s').*)
(*
Lemma OutDep_iff : forall aa, OutDep aa <-> OutDep2 aa.
Proof.
rewrite /OutDep2. elim.
- split. intros. inversion H. move => [] a [] a' [] x []. intros.  inversion a0. 
- intros. split.
 * intros. inversion H0. subst. exists a,a1,nil. rewrite /= andbC /=. split. done. apply/orP. done. 
 * subst. apply H in H4.  move : H4 => [] a0 [] a' [] s' [] []. intros.  subst. exists a0,a',s'. split. subst. rewrite /=. split. done. apply/andP. split. apply/orP. done. 
   applymove => [] a2 [] a' [] s'. [::a1]. split;auto. rewrite /=. rewrite andbC /=. apply/orP. done. done.
 * subst. apply H in H4. case : H4. move => [] a0 [] s' [] HH0 HH1 Hlt.  split. exists a. exists (a0::s'). rewrite HH0.  split;auto. 
   rewrite /=. case : HH0.  intros. subst. apply/andP. split. apply/orP. done. done. done. 

 * move => [] [] a0 [] s' [] HH0 HH1 Hlt. inversion HH0. subst. case : s' HH0 H HH1 Hlt. 
  ** intros. done. 
  ** simpl. intros. move : (andP HH1)=> []. move/orP. intros. constructor. done. apply/H. split. exists a. exists l. auto. exists a. a0 s'. subst. intros. case : a0. move : (H H4). split. exists a , (a1::aa). split;auto. rewrite /=.*)

(*Definition label_indDef := [indDef for label_rect].
Canonical label_indType := IndType label label_indDef.
Definition label_eqMixin := [derive eqMixin for label].
Canonical label_eqType := EqType label label_eqMixin.*)

Definition in_action p a := let: Action p0 p1 k :=a in  (p==p0) || (p==p1).

Definition pred_of_action (a : action) : {pred ptcp} := fun p => in_action p a.

Canonical action_predType := PredType pred_of_action. 

Coercion to_action (l : label) : action := l.1.

(*Definition act_of_label l := 
match l with 
| LU a _ => a
| LN a _ => a
end.*)

Definition pred_of_label (l : label) : {pred ptcp} := fun p => in_action p l.

Canonical label_predType := PredType pred_of_label.  





Inductive Tr : seq action -> sgType -> Prop :=
| TR_nil G : Tr nil G 
| TRMsg a u aa g0 : Tr aa g0 -> Tr (a::aa) (SGMsg a u g0)
| TRBranch a gs n aa : Tr aa (nth SGEnd gs n) ->  Tr (a::aa) (SGBranch a gs).
Hint Constructors Tr.
(*Fixpoint tr (ls : seq action) (sg : sgType)  {struct ls}  :=
match sg,ls with 
| _,nil => true
| SGMsg a u sg', a'::nil => (a == a')
| SGBranch a sgs, a'::nil => (a == a')
| SGMsg a u sg', a'::ls' => (a == a') && (tr ls' sg')
| SGBranch a sgs, a'::ls' => (a == a') && has (fun g => tr ls' g) sgs
| _,_ => false
end.*)


(*Definition trace_clash aa' := exists a0 aa a', aa' = a0::(rcons aa a') /\ same_ch a0 a'.*)

(*Definition Linear (sg : sgType) := forall aa_p a0 aa a1, Tr (aa_p ++ (a0::aa++[::a1])) sg -> same_ch a0 a1 -> 
exists mi mo, size mi = size mo /\ size mi = size aa /\ InDep (a0::((mask mi aa)++[::a1])) /\ 
                                                OutDep (a0::((mask mo aa))++[::a1]).*)
Definition exists_depP  (Pm : seq bool -> Prop) (P : seq action -> Prop) a0 aa a1 := exists m, size m = size aa /\ P (a0::((mask m aa))++[::a1]) /\ Pm m.
Notation exists_dep := (exists_depP (fun _ => True)).


Definition Linear (sg : sgType) := forall aa_p a0 aa a1, 
Tr (aa_p ++ (a0::aa++[::a1])) sg -> 
same_ch a0 a1 -> 
exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.
Print sum.
Definition value_nat := (@sum value nat).
Identity Coercion value_nat_coercion : value_nat >-> sum.

(*FunClass coercion*)
(*Parameter (c : ch) (p : ptcp). Check Action.
Inductive my_prod (A B : Set) := my_pair : A -> B -> my_prod A B.
Coercion nat_value_nat (n : nat) :  @sum value nat := inr n.
Coercion value_value_nat (v : value) :  @sum value nat := inl v.
Parameter (a : action).
Check (0 : value_nat).
Definition my_prod2 := @prod action value_nat. Print prod.

Check (my_pair a 0 : my_prod action value_nat).  : (nat * bool) % type).



Check ((0, true) : value_nat* true).
Definition action_vn := @prod action value_nat.
Identity Coercion prod_coercion : action_vn >-> prod.

Coercion nat_test : (a : action) (n : nat) *)
Unset Elimination Schemes. 
Inductive step : sgType -> label  -> sgType -> Prop :=
 | GR1 (a : action) u g : step (SGMsg a u g) (a, inl u) g
 | GR2 a n d gs : n < size gs -> step (SGBranch a gs) (a, inr n) (nth d gs n)
 | GR3 a u l g1 g2 : step g1 l g2 -> ptcp_to a \notin l -> step (SGMsg a u g1) l (SGMsg a u g2)
 | GR4 a l gs gs' : Forall2 (fun g g' => step g l g') gs gs' -> (ptcp_to a) \notin l  ->  step (SGBranch a gs) l (SGBranch a gs').
Set Elimination Schemes. 
Hint Constructors step. 

Lemma step_ind
     :  forall P : sgType -> label -> sgType -> Prop,
       (forall (a : action) (u : value) (g : sgType), P (SGMsg a u g) (a, inl u) g) ->
       (forall (a : action) (n : nat) (d : sgType) (gs : seq sgType),
        n < size gs -> P (SGBranch a gs) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (l : label) (g1 g2 : sgType),
        step g1 l g2 ->
        P g1 l g2 -> ptcp_to a \notin l -> P (SGMsg a u g1) l (SGMsg a u g2)) ->
       (forall (a : action) (l : label) (gs gs' : seq sgType),
        Forall2 (fun g : sgType => step g l) gs gs' ->  Forall2 (fun g0 g2 : sgType => P g0 l g2) gs gs' -> 

        ptcp_to a \notin l -> P (SGBranch a gs) l (SGBranch a gs')) ->
       forall (s : sgType) (l : label) (s0 : sgType), step s l s0 -> P s l s0.
Proof.
move => P H0 H1 H2 H3. fix IH 4.
move => ss l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f;auto.  
Qed.


Unset Elimination Schemes. 
Inductive stepG : sgType -> sgType -> label  -> sgType -> Prop :=
| GGR1 a u g0 : stepG (SGMsg a u g0) (SGMsg a u SGEnd) (a, inl u) g0
| GGR2 a d gs n : n < size gs -> stepG (SGBranch a gs) (SGBranch a nil) (a, inr n) (nth d gs n)
| GGR3 a u  g G l g' : stepG g G l g'  -> (ptcp_to a) \notin l ->
                     stepG (SGMsg a u g) (SGMsg a u G) l (SGMsg a u g')
| GGR4 a gs GS gs' l : Forall3 (fun g G g' => stepG g G l g') gs  GS gs' -> (ptcp_to a) \notin l -> stepG (SGBranch a gs) (SGBranch a GS) l (SGBranch a gs').
Hint Constructors stepG.
Set Elimination Schemes. 
Lemma stepG_ind
     : forall P : sgType -> sgType -> label -> sgType -> Prop,
       (forall (a : action) (u : value) (g0 : sgType),
        P (SGMsg a u g0) (SGMsg a u SGEnd) (a, inl u) g0) ->
       (forall (a : action) (d : sgType) (gs : seq sgType) (n : nat),
        n < size gs -> P (SGBranch a gs) (SGBranch a nil) (a, inr n) (nth d gs n)) ->
       (forall (a : action) (u : value) (g G : sgType) (l : label) (g' : sgType),
        stepG g G l g' ->
        P g G l g' ->
        ptcp_to a \notin l -> P (SGMsg a u g) (SGMsg a u G) l (SGMsg a u g')) ->
       (forall (a : action) (gs GS gs' : seq sgType) (l : label),
        Forall3 (fun g G : sgType => stepG g G l) gs GS gs' ->
        Forall3 (fun g G g' : sgType => P g G l g' ) gs GS gs' ->
        ptcp_to a \notin l -> P (SGBranch a gs) (SGBranch a GS) l (SGBranch a gs')) ->
       forall (s s0 : sgType) (l : label) (s1 : sgType), stepG s s0 l s1 -> P s s0 l s1.
Proof.
move => P H0 H1 H2 H3. fix IH 5.
move => ss s0 l s1 [].
intros. apply H0;auto. 
intros. apply H1;auto.
intros. apply H2;auto.
intros. apply H3;auto. elim : f. done. intros. constructor. apply IH. done. done.
Qed.


(*Should be split into pred and size lemmas*)
Lemma Forall3_forall_n : forall A B C (P : A -> B -> C -> Prop) (l0 : seq A) (l1 : seq B) (l2 : seq C) da db dc, Forall3 P l0 l1 l2 -> (forall n, n < size l0 -> P (nth da l0 n) (nth db l1 n) (nth dc l2 n)) /\ size l0 = size l1 /\ size l1 = size l2.  
Proof.
intros. elim : H. rewrite /=. split;auto. intros.  done.
rewrite /=. intros. move : H1 => [] H2 [] H3 H4. split;auto. case. rewrite /=. done. move => n. rewrite /=.
intros. have : n < size l. done. intros. apply H2. done. 
Qed.

Lemma Forall3_forall_n_def : forall A B C (P : A -> B -> C -> Prop) (l0 : seq A) (l1 : seq B) (l2 : seq C) da db dc, P da db dc -> Forall3 P l0 l1 l2 -> (forall n, n <= size l0 -> P (nth da l0 n) (nth db l1 n) (nth dc l2 n)) /\ size l0 = size l1 /\ size l1 = size l2.  
Proof.
intros. elim : H0. rewrite /=. split;auto. intros.  rewrite !nth_nil. done.
rewrite /=. intros. move : H2 => [] H4 [] H5 H6. split;auto. case. rewrite /=. done. move => n. rewrite /=.
intros. have : n <= size l. done. auto.  
Qed.



Lemma step_G : forall g l g',  step g l g' -> exists G, stepG g G l g'.
Proof. 
fix IH 4. intros. case : H; try solve [intros;econstructor;eauto].
- intros. case  : (IH _ _ _ s). intros. exists (SGMsg a u x). eauto. 
- intros. 
 have : exists GS, Forall3 (fun g G g' => stepG g G l0 g') gs GS gs'. 
 * elim : f.
  **  exists nil. done. 
  **  intros. case : (IH _ _ _ H).  intros. case : H1. intros. exists (x0::x1). eauto. 
 *  case. intros. exists (SGBranch a x);eauto. 
Qed.

Lemma G_step : forall g G l g', stepG g G l g' -> step g l g'.
Proof.
fix IH 5. 
intros. case : H; try solve [intros;constructor;auto].
intros. constructor;eauto. Guarded. 
intros. constructor. elim : f. done. intros. constructor. eauto. 
done. done. 
Qed.

Lemma linear_sgmsg : forall a u g0, Linear (SGMsg a u g0) -> Linear g0.
Proof. 
move => a u g0. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (SGMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.

Lemma nth_def : forall A (l : seq A) n d0 d1 , n < size l -> nth d0 l n = nth d1 l n.
Proof.
move => A. elim.
- case;done. 
intros. case : n H0. done. rewrite /=. intros. apply H. done. 
Qed.

Lemma linear_branch : forall a gs, Linear (SGBranch a gs) -> forall n d, n < size gs -> Linear (nth d gs n).
Proof.
intros. rewrite /Linear. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (SGBranch a gs). eauto. 
intros. apply TRBranch with (n:=n). erewrite nth_def. eauto. done. intros. apply : H. move : x. rewrite -cat_cons. intros. apply : x. done. 
Qed.




Lemma Tr_reduce : forall  G g l g', stepG g G l g' -> forall s, Tr s G -> Tr s g.
Proof.
intros. move :  H s H0.  elim. 
- intros. inversion H0. done. subst. inversion H2. subst. eauto.   
- intros.  inversion H0.  done. subst. move : H3. rewrite nth_nil.  intros. inversion H3. subst. apply TRBranch with (n:=0). 
  done. 
- intros. inversion H2.  done. subst. constructor. eauto.  
- intros. inversion H2. subst. done. subst.
  move : (@Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0) => [] H8 [] H9 H10.  

(*move : (@Forall3_forall_n _ _ _ (fun g0 g1 => fun _ => forall s, Tr s g1 -> Tr s g0) gs GS gs' d d d H0)=> [] H8 [] H9 H10.  *)
  case Heq : (n < size gs). 
 * move : (H8 n Heq). intros. apply TRBranch with (n:=n). apply H3. done. 
   have : size GS <= n. lia. intros. move : H5.  rewrite nth_default //=. intros. inversion H5. subst.
   apply TRBranch with (n:=n).  rewrite nth_default //=. rewrite H9. done. 
Qed.
Print stepG.

Lemma label_linear : forall g G l g',  stepG g G l g' -> Linear g -> Linear G.
Proof.
move => g G l g'. elim.
- move => a u g0 _.  rewrite /Linear. case. rewrite /=. intros. inversion H. subst. inversion H2. case : aa H H2 H3;done. 
  move => a0 l0 a1 aa a2. rewrite cat_cons. intros. inversion H. subst. inversion H2. apply List.app_cons_not_nil in H3.   done.
- move => a _ gs n Hlt HL. rewrite /Linear. intros. inversion H. apply List.app_cons_not_nil in H2. done. 
  subst. move : H3. rewrite nth_nil. intros. inversion H3. subst. exfalso. 
  clear H H0 H3.
  case : aa_p H1. rewrite /=. case. move => _ H3. apply List.app_cons_not_nil in H3. done.
  move => a2 l0.  rewrite cat_cons. case. move => _ H3. apply List.app_cons_not_nil in H3. done.
- move => a u g0 G0 l0 g'0. intros.  move : (linear_sgmsg H2). move/H0=> H3. 
  have : stepG (SGMsg a u g0) (SGMsg a u G0) l0 (SGMsg a u g'0). eauto. 
  move/Tr_reduce=> H4. move : H2. rewrite /Linear. 
  intros. apply : H2; eauto. 
- intros. have : stepG (SGBranch a gs) (SGBranch a GS) l0 (SGBranch a gs'). eauto. move/Tr_reduce=>H3.
  move : H2.  rewrite /Linear. intros. eauto.  
Qed.



Lemma Tr_or : forall s g, Tr s g \/ ~ (Tr s g).
Proof.
elim. intros. auto. 
intros. case : g. 
- right. move => H2. inversion H2. 
- intros. case : (H s).  case (eqVneq a a0). move =>->. auto. 
  right. move => H2. inversion H2. apply (negP i). by apply/eqP. 
- intros. right. move => H2. inversion H2. done. 
  intros. case : (eqVneq a a0). 
 * move => ->. elim : l0. case : l H.  intros. left. auto. apply TRBranch with (n:=0). rewrite nth_nil. done. 
   intros. right. move => H2. inversion H2.  rewrite nth_nil in H1. inversion H1. 
   intros. case : H0.  
  ** intros. left. inversion a2. subst. apply TRBranch with (n:=n.+1). rewrite /=. done. 
  ** intros. case : (H a1). intros. left. apply TRBranch with (n:=0).  done. 
     intros. right. move => H2. apply b. inversion H2. subst.  case : n H1. rewrite /=. done.
     intros. apply TRBranch with (n:=n). done. 
 * move/eqP=>H2. right. move => H3. apply H2. inversion H3. done. 
Qed.



Definition app_Forall3 {P : sgType -> sgType -> sgType -> Prop}{gs GS gs' : seq sgType} (H : Forall3 P gs GS gs') := @Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H.


Definition app_Forall3_def {P : sgType -> sgType -> sgType -> Prop}{gs GS gs' : seq sgType}  (H : Forall3 P gs GS gs') (H0 : P SGEnd SGEnd SGEnd) := @Forall3_forall_n_def _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0 H.



Lemma reduce_condition : forall g G l g', stepG g G l g' -> forall aa a' a, Tr (aa++([::a])) G ->  
a' \in aa -> (ptcp_to a') \notin l.  
Proof.
move => g G l g'. elim.
- intros. case : aa H H0; first done.  move => a1 l0. rewrite /=. intros. inversion H. subst. 
  inversion H2. contra_list. 
- intros.  case : aa H H0 H1; first done.  move => a1 l0. rewrite /=. intros. inversion H0. subst. 
  rewrite nth_nil in H3. inversion H3. contra_list.
- intros. case : aa H2 H3. done. move => a1 l1. rewrite cat_cons. intros. inversion H2. subst.
  move : H3. rewrite inE. move/orP=>[ /eqP ->  |  ]. done.  eauto. 
- intros. case : aa H2 H3. done. move => a1 l1. rewrite cat_cons. intros. 
  move : H3. rewrite inE. move/orP=>[ /eqP ->  |  ]. inversion H2.  subst. eauto.
  move : (app_Forall3 H0)=> []. intros. inversion H2.  subst.
  case Heq : (n < size gs). apply : a2. eauto. eauto. done. 
  rewrite nth_default in H4. inversion H4. contra_list. lia.
Qed.
Check TRBranch.
Definition TRBranchn {gs aa} n a (H : Tr aa (nth SGEnd gs n)) := @TRBranch a gs n aa H.
Check TRBranchn.
Arguments TRBranchn {_} {_} n.
Check TRBranchn.


Lemma deletion : forall g G l g', stepG g G l g' -> forall s, Tr s g' -> ~ Tr s G -> exists s0 s1, s = s0++s1 /\ Tr (s0++(l.1)::s1) g /\ Tr (s0++([::l.1])) G.
Proof. 
move => g G l g'. elim.
- intros. exists nil. exists s. rewrite /=. auto.
- intros. exists nil. exists s. rewrite /=. split;auto. split. apply TRBranch with (n:=n). 
  move : H0. rewrite (nth_def _ SGEnd) //=. apply TRBranch with (n:=0).  done. 
- intros. inversion H2. 
 * subst. exfalso. apply H3. done. 
 * subst. have : ~Tr aa G0.  move => H7. apply H3. auto. move => H7. 
   move : (H0 aa H6 H7)=> [] s0 [] s1 [] -> H8. exists (a::s0). exists s1. rewrite cat_cons. split;auto.  rewrite cat_cons. auto. case : H8. intros. rewrite cat_cons. auto. 
- intros. inversion H2. subst. 
 *  exists nil. exists nil. rewrite /=. exfalso. eauto. 
 * subst. move :  (@Forall3_forall_n _ _ _ _ gs GS gs' SGEnd SGEnd SGEnd H0).   
   move => [] Hall Hsize.
   have : ~Tr aa (nth SGEnd GS n). move => HH. apply H3. eauto. move => HH.
   case Heq : (n < size gs).
   move : (Hall n Heq aa H6 HH)=> [] s0 [] s1 [] -> [] HH0 HH1. 
   exists (a::s0). exists s1. rewrite /=. eauto. 
   rewrite nth_default in H6. inversion H6.  subst. rewrite nth_default in HH. done. 
   lia. lia. 
Qed.


Lemma split_list : forall A (l : seq A), l = nil \/ exists l' a, l = l'++([::a]).
Proof.
move => A. elim.
auto.  move => a l [] . move =>->. right.  exists nil. exists a. done. 
move => [] l' [] a0 ->. right. exists (a::l'). exists a0. done.
Qed.

Lemma Tr_app : forall l0 l1 G, Tr (l0++l1) G -> Tr l0 G.
Proof.
elim. rewrite /=. done.
move => a l IH l1 G. rewrite cat_cons. move => H. inversion H. 
- subst. constructor. eauto.  
- subst. apply TRBranch with (n:=n). eauto.
Qed.

Lemma last_eq : forall A (l0 l1 : seq A) x0 x1, l0 ++ ([::x0]) = l1 ++ ([::x1]) -> l0 = l1 /\ x0 = x1.
Proof.
move => A. elim.
case. rewrite /=. move => x0 x1. case. done.
move => a l x0 x1. rewrite /=. case. move =>-> H. apply List.app_cons_not_nil in H. done. 
rewrite /=. intros. case : l1 H0.  rewrite /=. case. move => _ /esym H1. apply List.app_cons_not_nil in H1. done. 
intros. move : H0.  rewrite cat_cons. case. intros. move : (H _ _ _ H1). case. intros. split. subst. done. done. 
Qed.


  

Lemma split_mask : forall A (l0 : seq A) x l1 m, size m = size (l0++x::l1) ->
mask m (l0 ++ x :: l1) =
  mask (take (size l0) m) l0 ++ (nseq (nth false m (size l0)) x) ++ mask (drop (size l0).+1 m) l1.
Proof.
move => A. elim. 
- rewrite /=. intros. rewrite take0 /=. case : m H. done. 
  intros. by  rewrite mask_cons /= drop0. 
- rewrite /=. intros. case : m H0.  done. rewrite /=. intros. 
  case : a0. rewrite cat_cons. f_equal. rewrite H //=. lia. 
  rewrite H //=. lia.
Qed.

Lemma add_sub : forall n1 n0, n0 = n0 + n1 - n1. 
elim.
lia. 
intros. lia. 
Qed.

Lemma in_mem_action_p : forall (p1 : ptcp) p2 c0 b, p1 \in ((Action p1 p2 c0, b): label).
Proof.
intros. rewrite /in_mem /=. by rewrite /pred_of_label /= eqxx. Qed.

Lemma in_mem_action_p2 : forall (p1 : ptcp) p2 c0 b, p2 \in ((Action p1 p2 c0, b): label).
Proof.
intros. rewrite /in_mem /=. by rewrite /pred_of_label /= eqxx orbC. Qed.


Hint Resolve in_mem_action_p in_mem_action_p2.

Lemma contra1 : forall a (l0 : label), II a l0 -> (ptcp_to a) \notin l0 -> False.
Proof.
case. move => p p0 c []; rewrite /II /=;intros; apply : (negP H0).   destruct a. simpl in H. rewrite (eqP H). auto. 
Qed.

Lemma contra2 : forall a (l0 : label), IO a l0 -> (ptcp_to a) \notin l0 -> False.
Proof.
case. move => p p0 c []; rewrite /IO /=;intros; apply : (negP H0). destruct a. simpl in H.  rewrite (eqP H). auto. 
Qed.

Lemma split_indep : forall s a0 a1 s2, InDep (s++a0::a1::s2) -> InDep (a0::a1::s2).
Proof.
elim. auto. rewrite /=. intros. apply H. inversion H0. subst. case : l H3 H0 H.  rewrite /=. intros. done.
rewrite /=. intros. case : H3. intros. apply List.app_cons_not_nil in H3. done. done.
Qed.

Lemma in_action_to : forall a, in_action (ptcp_to a) a.
Proof.
case. intros. by rewrite/= eqxx orbC.
Qed. 

Lemma in_action_from : forall a, in_action (ptcp_from a) a.
Proof.
case. intros. by rewrite/= eqxx.
Qed. 

Lemma cons23 : forall A  s0 s1 aa (a0 : A) a1,  a0 :: aa ++ [:: a1] = s0 ++ s1 -> s0 = nil /\ a0::aa++([:: a1]) = s1 \/ s1 = nil /\  a0::aa++([:: a1]) = s0 \/ exists s0' s1', s0 = a0::s0' /\ s1 = s1'++([::a1]) /\ s0' ++ s1' =  aa.
Proof.
move => A. elim.
move => s1 aa a0 a1. rewrite /=. move => <-. auto. 
rewrite /=. intros. case : H0. move => <-. case : aa. rewrite /=. case : s1. rewrite cats0. move => <-. auto. 
move => a2 l0. right. right. exists l. case : l H H0. rewrite /=. intros. exists nil. done. 
rewrite /=. intros. case : H0.  intros. apply List.app_cons_not_nil in H1. done. 
move => a2 l0. rewrite cat_cons. move/H. case. 
- case. move => -> <-. right. right. exists nil. exists (a2::l0). done. 
case. 
 - case. move => -> <-. auto. 
 - case.  move => x [] x1 [] -> [] -> H1. right. right. exists (a2::x). exists x1. rewrite /= H1. done. 
Qed.


Lemma InDep_app : forall l0 l1, InDep (l0 ++ l1) -> 1 < size l1 -> InDep l1.
Proof.
elim. rewrite /=. done.
move => a l IH l1. rewrite cat_cons. move => H. inversion H. subst.
case : l H2 H IH.  rewrite /=. move => <-. done. 
move => a0 l. rewrite cat_cons. case. move => <-. case : l.  case : l1. done. done. done. 
intros. subst. rewrite H1 in H3. auto. 
Qed.

Definition IO_II a0 a1 := IO a0 a1 || II a0 a1.

Lemma ind_aux : forall l a a0, path IO a (belast a0 l) -> II (last a (belast a0 l)) (last a0 l) -> IO_II a a0 && path IO_II a0 l.
Proof.
 elim.
- move => a a0.  rewrite /= /IO_II. move => _ ->.  by rewrite orbC.
- move => a l IH a0 a1. rewrite /=. move/andP=>[].  intros. rewrite /IO_II a2 /=.
  unfold IO_II in IH. apply/IH. done. done. 
Qed.

Lemma indep0 : forall l0 l1, indep (l0 ++ l1) -> if l0 is x::l0' then path IO_II x l0' else true.
Proof.
move => l0 l1. rewrite /indep.
case :l0 ;first done.
move => a l. rewrite /=. case : l;first done.
move => a0 l. rewrite /=. move/andP=> [] H H1. elim : l a a0 H H1.
- move => a a0. rewrite /=.  case : l1. simpl. rewrite /IO_II. move => _ -> . by rewrite orbC.  
  move => a1 l. rewrite/= /IO_II. by move/andP=> [] ->.
- move => a l IH a0 a1. rewrite /= /IO_II. move/andP=> [] ->. intros. rewrite /=. 
  unfold IO_II in IH. apply/IH. done. done.
Qed.


Lemma indep1 : forall l0 l1, indep (l0 ++ l1) -> if l1 is x::l1' then path IO_II x l1' else true.
Proof.
case. simpl. case. done. rewrite /=. move => a []. done.
move => a0 l. rewrite /=. intros. move : H. move/andP=>[]. intros. apply/ind_aux. done. done. 
- move => a l l1. rewrite /=. case : l. rewrite /=. case : l1. done.
  intros. move : H=> /andP=> [] []. intros. move : (ind_aux a1 b). by move/andP=>[].
- move => a0 l. rewrite /=. move/andP=> []. intros. case : l1 a1 b. done. 
intros. move : (ind_aux a2 b). move/andP=> []. rewrite cat_path. move => _ /andP => [] []. 
  rewrite /=. move => _ /andP => [] []. done. 
Qed.


Inductive IO_seq : seq action -> Prop :=
 | IO_seq0 a b : IO a b ->  IO_seq ([::a; b])
 | IO_seq1 a b l : IO a b -> IO_seq (b::l) -> IO_seq (a::b::l).


Lemma apply_InDep_app : forall l l0 l1 , InDep l -> l = l0++l1 -> 1 < size l1 -> InDep l1.
Proof.
intros.  apply : InDep_app;auto. rewrite H0 in H. eauto. 
Qed.

Lemma OutDep_app : forall l0 l1, OutDep (l0 ++ l1) -> 1 < size l1 -> OutDep l1.
Proof.
elim. rewrite /=. done.
move => a l IH l1. rewrite cat_cons. move => H. inversion H. subst.
case : l H2 H IH.  rewrite /=. move => <-. done. 
move => a0 l. rewrite cat_cons. case. move => <-. case : l.  case : l1. done. done. done. 
intros. subst. rewrite H1 in H3. auto. 
Qed.

Lemma outdep0 : forall l0 l1, outdep (l0 ++ l1) -> if l0 is x::l0' then path IO_OO x l0' else true.
Proof.
rewrite /outdep. case;first done. 
move => a l l1. rewrite cat_cons. case : l;first done.  
move => a0 l. rewrite cat_cons. rewrite -cat_cons. rewrite cat_path. by move/andP=>[]. 
Qed.

Lemma nil_ll : forall A (l0 l1 : seq A), nil = l0 ++ l1 -> l0 = nil /\ l1 = nil.
Proof.
move => A. elim.
- case. done. done. 
- rewrite /=. done. 
Qed.

Check list_ind.


Lemma apply_OutDep_app : forall l l0 l1 , OutDep l -> l = l0++l1 -> 1 < size l1-> OutDep l1.
Proof.
intros.  apply : OutDep_app;auto. rewrite H0 in H. eauto. 
Qed.

Lemma delete_middle : forall a0 l0 a l1 a1 P, exists_depP (fun m => nth false m (size l0) = false) P a0 (l0 ++ a::l1) a1 ->
                      exists_dep P a0 (l0++l1) a1.
Proof.
intros. move : H => [] m [] H0 [] H1 H2. exists ((take (size l0) m)++(drop (size l0).+1 m)).
rewrite size_cat size_take size_drop H0 !size_cat /=. have : size l0 < size l0 + (size l1).+1 by lia.
move => H3. rewrite H3. split. lia. split;auto. move : H1. rewrite !split_mask //=. rewrite H2 /= mask_cat //=. 
by rewrite size_take H0 size_cat /= H3. 
Qed.


Lemma apply_linear : forall g s_tr a_p a0 s a1, Linear g -> Tr s_tr g -> s_tr = a_p++(a0::s++[::a1]) -> same_ch a0 a1 -> exists_dep InDep a0 s a1 /\ exists_dep OutDep a0 s a1.
Proof.
intros. rewrite H1 in H0. eauto. 
Qed.

Lemma get_neigbor : forall (P : action -> action -> bool) a p x_end m, path P a ((mask m p)++[::x_end]) -> exists x_in, x_in \in (a::p) /\ P x_in x_end. 
Proof. 
intros. 
case : (split_list (mask m p)) H. move =>->. rewrite /= andbC /=. intros. exists a. by rewrite inE eqxx /=.
move => [] l' [] a0 Heqa2.  move : (Heqa2) =>->. rewrite -catA. rewrite cat_path /=.
move/andP=> [] _ /andP => [] [] _. rewrite andbC /=. move => HH.
have : a0 \in a::p. rewrite inE.  apply/orP. right. apply (@mem_mask _ _  m). 
rewrite Heqa2. by rewrite mem_cat inE eqxx orbC. 
intros. exists a0. by rewrite x. 
Qed.

Lemma IO_II_in_action : forall a0 (l : label), IO_II a0 l -> in_action (ptcp_to a0) l.
Proof.
move => a0 a1. rewrite /IO_II. move/orP=>[]. rewrite /IO. move/eqP=>->. apply in_action_from.
rewrite /II. move/eqP=>->. apply in_action_to.
Qed.

Lemma in_split : forall (A : eqType) l (x : A), x \in l -> exists l0 l1, l = l0 ++ x::l1.
Proof.
move => A. elim. done.
move => a l IH x. rewrite inE. move/orP=>[]. move/eqP=>->. exists nil. exists l. done. move/IH=> [] l0 [] l1 ->. exists (a::l0),l1. done. 
Qed. 

(*Can be simplified more*)
Lemma in_label : forall (l : label), ptcp_from l.1 \in l.
Proof.
case. intros. rewrite /=. destruct a. simpl. done.
Qed.

Hint Resolve in_label.

Lemma stepG_aux : forall g G l g', stepG g G l g' -> Linear g -> 
forall a0 aa a1, Tr (a0 :: aa ++ [:: a1]) g' -> same_ch a0 a1 -> exists_dep InDep a0 aa a1 /\ exists_dep OutDep a0 aa a1.
Proof.
move => g G l g'  Hstep  Lg a aa a1 HG Hch.
move : (label_linear Hstep Lg) =>LG. case : (Tr_or (a:: aa ++ ([:: a1])) G); first auto using (LG nil).
   move => Hnot.  
   move : (deletion Hstep HG Hnot)=> [] s0 [] s1 [] Heq [] Hg0 HG0.
   case : (cons23 Heq). 
   move => [] Hs0 Hs1;subst; simpl in *. have : Tr (([::l.1]) ++ (a::aa) ++  ([::a1])) g. by  simpl. move => Hg0'.  apply : Lg. apply : Hg0'. done. 
   case; first ( move => [] Hs0 Hs1; subst; apply : (LG nil); simpl; eauto using Tr_app). 
   move => [] s0' [] s1' [] Hs0 [] Hs1 Heqaa. subst. simpl in *. 
   move : (@apply_linear _ _ nil a (s0' ++ (l.1)::s1') a1 Lg Hg0).  (*get that original g contains in/out chains*)
   rewrite /= -!catA cat_cons. move => Hinout. move : (Hinout Logic.eq_refl Hch)=> [] Hin Hout. 
   rewrite  -cat_cons -[_::_]cat0s in HG0. (*make it ready to by used with LG*)
   split.
   ** move : Hin => [] m [] Hsize [] Hin _. (*InDep*)
      case Heqb : (nth false m (size s0')); last (apply : delete_middle; exists m; split;eauto). 
      move : Hin. rewrite split_mask //= Heqb /=.


      move/InDep_iff.
      have : (a :: (mask (take (size s0') m) s0' ++ l.1 :: mask (drop (size s0').+1 m) s1') ++ [:: a1]) =
             (((a :: (mask (take (size s0') m) s0' ++ [::l.1])) ++ (mask (drop (size s0').+1 m) s1') ++ [:: a1])).
      by rewrite /= -!catA. move =>->.

      move/indep0. move/get_neigbor=> [] x_in []. intros.

      exfalso. apply/negP. eapply reduce_condition with (a':=x_in). apply : Hstep.   apply : HG0. 
      by rewrite mem_cat a0 orbC. apply IO_II_in_action. done. 

  ** move : Hout => [] m [] Hsize [] Hout _. (*OutDep*) 
     case Heqb : (nth false m (size s0')); last (apply : delete_middle; exists m; split;eauto).
     move : Hout. rewrite split_mask //= Heqb /=.

     move/OutDep_iff.
      have : (a :: (mask (take (size s0') m) s0' ++ l.1 :: mask (drop (size s0').+1 m) s1') ++ [:: a1]) =
             (((a :: (mask (take (size s0') m) s0' ++ [::l.1])) ++ (mask (drop (size s0').+1 m) s1') ++ [:: a1])).
      by rewrite /= -!catA. move =>->.

      move/outdep0. move/get_neigbor=> [] x_in []. intros. 
      rewrite /IO_OO in b. case : (orP b). intros.  exfalso. apply : negP. eapply reduce_condition with (a':= x_in). apply : Hstep.
      apply : HG0. by rewrite mem_cat a0 orbC. move : a2. rewrite /IO. move/eqP=>->. auto.  

      rewrite /OO. move/andP=> [] /eqP _ HH0. 
      move : (in_split a0)=> [] l1 [] l2 Heq0. have : x_in \in [::] ++ a :: s0' by rewrite mem_cat a0 orbC. move => xin. Check reduce_condition. move : (@reduce_condition _ _ _ _ Hstep _ _ _ HG0 xin )=> not_act. 
  simpl in HG0. rewrite -cat_cons Heq0 -catA in HG0. 
      
        move : (LG _ _ _ _ HG0 HH0) => [] HInm HOutm. move : HInm => [] mm [] Hsizem  [] HInm _.
        move : HInm. move/InDep_iff. 
     case : (split_list (mask mm l2)). move=>->. rewrite /= /II. move/eqP=> HHeq.  exfalso. apply :negP. apply : not_act. 
        rewrite HHeq. apply/in_action_to.  
     move => [] l' [] a2 Heq2. rewrite Heq2 -!catA -cat_cons. move/indep1. rewrite /= andbC /=. move => HIO_II.  exfalso. apply : negP. 
     eapply reduce_condition with (a':=a2). apply Hstep. rewrite catA in HG0.  apply : HG0.
     rewrite mem_cat. apply/orP. right. rewrite inE. apply/orP. right. apply (@mem_mask  _ _ mm). rewrite Heq2.
     by rewrite mem_cat inE  eqxx orbC. apply IO_II_in_action.  done.
Qed.


Lemma stepG_linear : forall g G l g', stepG g G l g' -> Linear g -> Linear g'.
Proof.
move => g G l g'. elim.  
- eauto using linear_sgmsg.
- eauto using linear_branch.  
- intros. rewrite /Linear. case.
 * eauto using stepG_aux. 
 * intros. simpl in H3. inversion H3;subst. apply : H0;eauto using linear_sgmsg. 
- intros. rewrite /Linear. case.
 * eauto using stepG_aux.
 * intros. simpl in H3. inversion H3;subst.
   move : (app_Forall3 H0)=>[] HH HH1.
   case Heq : (n < size gs).
  **  apply : HH;eauto using linear_branch.  
  ** rewrite nth_default in H6; last lia.  inversion H6. by move : H7=> /nil_ll  => [] []. 
Qed.
