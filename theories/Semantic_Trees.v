From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import finmap.

From Paco Require Import paco.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From deriving Require Import deriving.
From Dep Require Import Global_Syntax Linearity.



Inductive dir := Sd | Rd.
Unset Elimination Schemes. 
CoInductive seType  : Type :=
  | SEEnd : seType  
  | SEMsg : dir -> ch -> value -> seType -> seType
  | SEBranch : dir -> ch ->  seq seType -> seType.
Set Elimination Schemes.


Inductive co_projF (R : sgType -> ptcp -> seType -> Prop) : sgType -> ptcp -> seType -> Prop :=
| cp_msg_from g p0 e p1 c u : R g p0 e -> co_projF R (SGMsg (Action p0 p1 c) u g) p0 (SEMsg Sd c u e)
| cp_msg_to g p0 e p1 c u : R g p1 e -> co_projF R (SGMsg (Action p0 p1 c) u g) p1 (SEMsg Rd c u e)
| cp_msg_other g a e  u p : ~in_action p a -> R g p e -> co_projF R (SGMsg a u g) p e
| cp_branch_from gs es p0 p1 c : Forall2 (fun g e => R g p0 e) gs es -> 
                                 co_projF R (SGBranch (Action p0 p1 c) gs) p0 (SEBranch Sd c es)
| cp_branch_to gs es p0 p1 c : Forall2 (fun g e => R g p1 e) gs es -> 
                               co_projF R (SGBranch (Action p0 p1 c) gs) p1 (SEBranch Rd c es)
| cp_branch_other gs p e a :  ~~ in_action p a -> Forall (fun g => R g p e) gs -> 
                               co_projF R (SGBranch a gs) p e.
Hint Constructors co_projF.


Lemma co_proj_mono : monotone3 co_projF.
Proof.
move => x y. intros. inversion IN;subst;eauto.
apply/cp_branch_from. induction H;auto.  
apply/cp_branch_to. induction H;auto. 
apply/cp_branch_other. done. induction H0;auto. 
Qed.

Hint Resolve co_proj_mono : paco.
Notation  co_proj := (paco3 co_projF bot3).


Open Scope fmap_scope.

Definition env := {fmap ptcp -> seType}.  

Inductive co_allprojF (R : sgType -> env -> Prop) : sgType ->  env -> Prop :=
| all_end  (d : env) : (forall p, p \in d -> d.[? p] = Some SEEnd)  -> co_allprojF R SGEnd d
| all_msg g (Δ : env) p0 p1 e0 e1 c u : R g Δ -> Δ.[? p0] = Some e0 -> Δ.[? p1] = Some e1 -> co_allprojF R (SGMsg (Action p0 p1 c) u g) 
                                                                Δ.[p0 <- SEMsg Sd c u e0].[p1 <- SEMsg Rd c u e1]
| all_branch (p0 p1 : ptcp) es0 es1 c (Δ : env) (Δs : seq env) gs  : Forall2 R gs Δs -> Forall2 (fun (d : env) e => d.[? p0] = Some e) Δs es0 -> Forall2 (fun (d : env) e => d.[? p1] = Some e) Δs es1 ->  Forall (fun d => d.[~ p0].[~ p1]  = Δ ) Δs ->
                                                          co_allprojF R (SGBranch (Action p0 p1 c) gs)            
                                                                        Δ.[p0 <- SEBranch Sd c es0]
                                                                         .[p1 <- SEBranch Rd c es1].
Hint Constructors co_allprojF.

Lemma Forall2_mono : forall (A B : Type) (l0 : seq A) (l1 : seq B) (r0 r1 : A -> B -> Prop),  Forall2 r0 l0 l1  -> (forall x y, r0 x y -> r1 x y) -> Forall2 r1 l0 l1.
Proof.
intros. induction H;auto.
Qed.

Hint Resolve Forall2_mono.

Lemma co_allproj_mono : monotone2 co_allprojF.
Proof.
move => x y. intros. inversion IN;subst;eauto.  
Qed.

Hint Resolve co_allproj_mono : paco.
Notation  co_allproj := (paco2 co_allprojF bot2).


Lemma all_proj_spec : forall g d p e, co_allproj g d -> d.[? p] = Some e <-> exists p, co_proj g p e. 
Proof. Admitted.


Inductive Estep : seType ->  (dir * ch * (value + nat))  -> seType -> Prop :=
| estep_msg d c v e0  : Estep (SEMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d vn c c' v e0 e0'  : Estep e0 (Sd,c,vn) e0' -> c <> c' -> Estep (SEMsg d c' v e0) (Sd,c,vn) (SEMsg d c' v e0')
| estep_branch n es d c  : n < size es -> Estep (SEBranch d c es) (d,c, inr n) (nth SEEnd es n)
| estep_branch_async es0 es1 vn d c c'  : Forall2 (fun e0 e1 => Estep e0 (Sd,c,vn) e1) es0 es1 -> c <> c' -> 
                                          Estep (SEBranch d c es0) (Sd,c,vn) (SEBranch d c es1).
Hint Constructors Estep.



(*Lemma to_label_eq : forall p0 p1 c v, to_label (inl v) p0 p1 c = LU (Action p0 p1 c) v. 
Proof. done. Qed. 

Lemma to_label_eq2 : forall p0 p1 c n, to_label (inr n) p0 p1 c = LN (Action p0 p1 c) n. 
Proof. done. Qed. *)


(*later update labels in step to be value + nat *)


Inductive EnvStep : env -> label -> env -> Prop := 
| envstep_rule (Δ : env) e0 e1 e0' e1' c vn p0 p1 : Estep e0 (Sd,c,vn) e0' ->  Estep e1 (Rd,c,vn) e1' ->  
                                     EnvStep Δ.[p0 <- e0].[p1 <- e1] (Action p0 p1 c, vn)  Δ.[p0 <- e0'].[p1 <- e1'].
Hint Constructors EnvStep.


Inductive non_reflF (P : sgType -> Prop) : sgType -> Prop :=
| nr_end : non_reflF P SGEnd
| nr_msg a u g0 : ptcp_from a <> ptcp_to a -> P g0 -> non_reflF P (SGMsg a u g0)
| nr_branch a gs : ptcp_from a <> ptcp_to a -> Forall P gs -> non_reflF P (SGBranch a gs).
Hint Constructors non_reflF.

Lemma non_reflF_mono : monotone1 non_reflF.
Proof.
move => x y. intros. inversion IN;auto. constructor. done. subst. induction H0;auto. 
Qed.

Hint Resolve non_reflF_mono : paco.
Notation non_refl := (paco1 non_reflF bot1).

Definition Coherent g := Linear g /\ (exists Δ, co_allproj g Δ) /\ non_refl g.


Lemma map_same : forall (d : env) p e, d.[? p] = Some e ->  d.[ p <- e] = d.
Proof.
intros. move : H. intros. apply/fmapP. intros. rewrite fnd_set.   destruct (k == p) eqn:Heqn. rewrite -H. rewrite (eqP Heqn). done. done. 
Qed.

Lemma index_Forall : forall (A: Type) (l0 : seq A) d0 n (P : A  -> Prop), n < size l0 -> Forall P l0 -> P (nth d0 l0 n).
Proof.
intros. move : H0 d0 n H. elim.
intros.  done. intros. destruct n. simpl. done. simpl. auto. 
Qed.



Lemma size_Forall2 : forall (A B : Type) (l0 : seq A) (l1 : seq B) P, Forall2 P l0 l1 -> size l0 = size l1. 
Proof. intros. induction H;simpl;auto. Qed.

Lemma index_Forall2 : forall (A B : Type) (l0 : seq A) (l1 : seq B) d0 d1 n (P : A -> B -> Prop), n < size l0 -> Forall2 P l0 l1 -> P (nth d0 l0 n) (nth d1 l1 n).
Proof.
intros. move : H0 d0 d1 n H. elim.
intros.  done. intros. destruct n. simpl. done. simpl. auto. 
Qed.

Open Scope fset_scope.

Lemma rem2_map : forall (d : env) p1 p2 e1 e2, d.[p1 <- e1].[p2 <- e2] = d.[\  p1 |` [fset p1]].[p1 <- e1].[p2 <- e2]. 
Proof.
intros. rewrite !setf_rem /=.
have : (p2 |` (p1 |` domf d)) `\` ([fset p1; p1] `\ p1 `\ p2) = (p2 |` (p1 |` domf d)).
apply/eqP. apply/fset_eqP. Locate "=i". Print eq_mem.  intro x. rewrite !inE /=. rewrite negb_and -!eqbF_neg. 
destruct (x == p2) eqn:Heqn. by rewrite /=. rewrite /=. destruct (x == p1). by rewrite /=. rewrite /=. done.
move=>->. have : p2 |` (p1 |` domf d) = domf ((d.[p1 <- e1]).[p2 <- e2]).  apply/eqP/fset_eqP. move => x. by rewrite /=.  
move => ->. Search _ (?a.[& _] = ?a). by rewrite restrictfT. 
Qed.


Lemma neg_sym : forall (A : eqType) (a b : A), (a != b) = (b != a).
Proof.
intros. destruct (eqVneq a b).  done. done. 
Qed.

Lemma neg_false : forall (A : eqType) (a b : A), a != b <-> a == b = false. 
Proof.
intros. case : (eqVneq a b);rewrite /=;intros;split;done.
Qed.


Lemma EnvStepdom : forall (d0 d1 : env) l, EnvStep d0 l d1 -> domf d0 = domf d1.
Proof.
intros.
inversion H. subst. rewrite /=.  done.
Qed.


(*(*Can't use in_find because seType is not a choice type*)
Lemma in_fnd2 : forall (d : env) k, k \in d -> exists e, d.[? k] = Some e.
Proof.
intros. destruct (d.[? k]) eqn:Heqn. exists s.  done. rewrite -fndSome in H. rewrite /isSome in H.   rewrite Heqn in H. done. 
Qed.*)

Lemma in_dom : forall (d : env) p e, d.[? p] = Some e -> p \in d.
Proof.
intros.
destruct (p \in d) eqn:Heqn. done. rewrite -fndSome in Heqn. rewrite /isSome in Heqn. rewrite H in Heqn. done.
Qed.

(*Lemma set_plus : forall (d : env) p e, d.[p <- e] = d + [fmap].[p <- e].
Proof.
intros. apply/fmapP. intros. Search _ ((_ + _) .[? _]). rewrite fnd_cat.  rewrite !fnd_set /=.  destruct (k == p) eqn:Heqn. /=. Search _ (_.[_ <- _].[? _]). = Some _). simpl. rewrite /=. rewrite inE.  rewrite /=.*)

Lemma notin_label : forall p a vn, p \notin ((a,vn) : label) = (p != (ptcp_from a)) && (p != (ptcp_to a)).

Proof.
intros. destruct a. by rewrite /= /in_mem /= /pred_of_label /= negb_or. 
Qed.

Lemma in_label : forall p a, p \in (a : label) = (p == (ptcp_from a)) || (p == (ptcp_to a)).
Proof.
intros. destruct a.  rewrite /= /in_mem /= /pred_of_label /= /in_action. by destruct a.
Qed.


Lemma EnvStep_weaken : forall (d0 d1 : env) l p e , EnvStep d0 l d1 -> p \notin l -> EnvStep d0.[p <- e] l d1.[p <- e].
Proof.
intros. inversion H. subst. rewrite notin_label in H0. move : (andP H0)=> [] /=.  intros.   
move : a b. rewrite !neg_false. intros.  
rewrite  [Δ.[_ <- _].[_ <- _].[_ <- _]]setfC H4.  rewrite  [Δ.[p0 <- _].[p <- _]]setfC H3. 
rewrite  [Δ.[p0 <- _].[p1 <- _].[_ <- _]]setfC H4. rewrite  [Δ.[p0 <- _].[p <- _]]setfC H3.
auto. 
Qed.

Lemma EnvStep_same : forall (d0 d1 : env) l p, EnvStep d0 l d1 -> p \notin l -> d0.[? p] = d1.[? p].
Proof.
intros. inversion H. subst. rewrite notin_label in H0. move : (andP H0) => [] HH [] HH0. rewrite !fnd_set. simpl in HH,HH0. have : p == p1 = false by lia.  move=>->. 
have : p == p0 = false by lia. move=>->. done.
Qed.


(*c <> c' assumption we get from linearity, how to port it to environments?*) 

Definition non_refla ( a : action) := ptcp_from a != ptcp_to a. 

Coercion action_to_ch (a : action) : ch := let: Action _ _ c := a in c.

Ltac red_if_w H := rewrite [_ == _]Bool.negb_involutive_reverse H /negb.
Ltac red_if := rewrite [_ == _]Bool.negb_involutive_reverse.

Lemma EnvStep_async : forall (d0 d1 : env) (l : label) (c' : ch) d  u e0 e1, c' <> l -> non_refla l ->  EnvStep d0 l d1 -> 
d0.[? ptcp_from l] = Some e0 -> d1.[? ptcp_from l] = Some e1 -> EnvStep d0.[ptcp_from l <- SEMsg d c' u e0] l d1.[ptcp_from l <- SEMsg d c' u e1].
Proof.
intros. inversion H1. subst. simpl in H0. unfold non_refla in H0. simpl in H0.
rewrite setfC /=. repeat red_if_w H0. rewrite [Δ.[_ <- _].[ p1 <- _].[p0 <- _]]setfC. 
red_if_w H0. 
rewrite [Δ.[p0 <- _].[p0 <- _]]setfC eqxx. rewrite [Δ.[p0 <- _].[p0 <- _]]setfC eqxx. 
move : H2 H3. rewrite !fnd_set /=. 
red_if_w H0. rewrite eqxx.  move=> [] HH [] HH0. subst.  
 have : c <> c'. 
  rewrite /action_to_ch /=. intros. move => HH. apply H. subst. done. 
auto.
Qed.


Lemma step_to_Estep : forall g l g' Δ,  step g l g' -> non_refl g -> co_allproj g Δ -> exists Δ', co_allproj g' Δ' /\ EnvStep Δ l Δ' .
Proof. 
move => g l g' Δ H. elim : H Δ.
- intros. punfold H. inversion H. punfold H0. inversion H0. subst. pclearbot.  exists Δ0.  split. inversion H9. done. done.
   rewrite -{2}(map_same H12)  -{2}(map_same H11). auto. 
- intros. punfold H1. inversion H1. punfold H0. inversion H0. subst. pclearbot. exists (nth [fmap] Δs n).  split. 
 * apply index_Forall2. done. 
 * apply (Forall2_mono H4). intros. inversion H2. done. done. 
 * have : (nth [fmap] Δs n).[? p0] = Some (nth SEEnd es0 n).  apply index_Forall2 with (l0:=Δs)(l1:= es0);auto.
   rewrite -(size_Forall2 H4) //=. intros.

   have : (nth [fmap] Δs n).[? p1] = Some (nth SEEnd es1 n).  apply index_Forall2 with (l0:=Δs)(l1:= es1);auto.
   rewrite -(size_Forall2 H4) //=. intros.  (*up until now just setup*)
   
   rewrite -(map_same x0). rewrite -(setf_rem1 (nth [fmap] Δs n) p1 (nth SEEnd es1 n)). (*pull p0 binding out in front*)
   rewrite -(map_same x). rewrite -(setf_rem1 (nth [fmap] Δs n) p0 (nth SEEnd es0 n)).  (*pull p1 binding out in front*)

   rewrite remf1_set. rewrite eq_sym. simpl in H11. move : H11. move/eqP. rewrite -eqbF_neg. move/eqP. move=>->. (*collect map restrictions before new bindings*)

   have : (((nth [fmap] Δs n).[~ p0]).[~ p1]) = Δ0. apply index_Forall;auto. by rewrite -(size_Forall2 H4). move=>->. (*replace restricted map with Δ0*)

   have : n < size es0 by  rewrite -(size_Forall2 H5) -(size_Forall2 H4). 
   have : n < size es1 by rewrite -(size_Forall2 H6) -(size_Forall2 H4). intros.  eauto. (*Now we reduce environments*)
- intros. punfold H2. inversion H2. pclearbot. punfold H3. inversion H3. subst. inversion H12;try done. 
   move : (H0 _ H8 H4)=> [] Δ' [] Hp' Step'. clear H0. simpl in H1,H6. clear H2. clear H8. clear H12. (*Setup*)
   move : (EnvStepdom Step')=> Hdom. 
   
   have : p0 \in Δ'. rewrite inE -Hdom.  apply : in_dom. eauto. 
   have : p1 \in Δ'. rewrite inE -Hdom.  apply : in_dom. eauto. intros. 
   move : (in_fnd x). move : (in_fnd x0). intros. (*Show Δ' is defined for p0 and p1*)
   exists (Δ'.[p0 <- SEMsg Sd c u Δ'.[x0]].[p1 <- SEMsg Rd c u Δ'.[x]]). split;auto. (*auto handles projection goal*)
   destruct (p0 \notin l0) eqn:Heqn.
   * rewrite -(EnvStep_same Step' Heqn) in in_fnd. rewrite -(EnvStep_same Step' H1) in in_fnd0.
     rewrite in_fnd in H14. rewrite in_fnd0 in H15. inversion H14. inversion H15. subst. 
     apply EnvStep_weaken;auto.
     apply EnvStep_weaken;auto.
   *  move : (negbFE Heqn). rewrite in_label. move/orP. case. 
     ** move/eqP.  intros. subst.  rewrite -(EnvStep_same Step' H1) in in_fnd0. rewrite in_fnd0 in H15. inversion H15.
       apply EnvStep_weaken;auto.  apply : EnvStep_async. 
     admit. (*Linearity condition*)
     admit. (*next show that a reduction from a global type that satisfies non_refl, will have a non_refl label*)
     done. 
     done.
     done.
  * intros. (*How to handle this case?*)
    admit.
- admit.
Admitted.


















(*Not used from this point on*)

Definition is_full_proj (d : env) g (P : ptcp -> Prop) := 
(forall p e, P p -> co_proj g p e -> d.[? p] = Some e) /\ (forall p, ~ P p -> d.[? p] = None).

Inductive rec_red : seType -> (dir * ch * (value + nat)) -> seType -> Prop :=
| rr_msg c v e0  : rec_red (SEMsg Rd c v e0) (c, inl v) e0
| rr_eb n es c : n < size es -> rec_red (SEBranch c es) (c, inr n) (nth SEEnd es n).
Hint Constructors rec_red.

Inductive send_red : seType ->  (ch * (value + nat))  -> seType -> Prop :=
| sr_msg c v e0  : send_red (SEMsg Sd c v e0) (c, inl v) e0
| sr_msg0 c c' v e0 e0' l ann : send_red e0 l e0' ->  c <> c' -> send_red (SEMsg Sd c v e0) (c', ann) (SEMsg Sd c v e0')
| sr_eb n es c  : n < size es -> send_red (SEBranch Sd c es) (c, inr n) (nth SEEnd es n)
| sr_eb0 es0 es1 c c' ann : Forall2 (fun e0 e1 => send_red e0 (c',ann) e1) es0 es1 -> c <> c' ->  send_red (SEBranch Sd c es0) (c',ann) (SEBranch Sd c es1).
Hint Constructors send_red.

(*Remove d'*)
Inductive ctx_red : env -> (action * (value + nat)) -> env -> Prop :=
| ctx_red_comm (d : env)  p0 p1 c e0 e0' e1 e1' ann : 
                 d.[? p0] = Some e0 -> d'.[? p0] = Some e0' ->  
                 d.[? p1] = Some e1 -> d'.[? p1] = Some e1'  -> 
                 send_red e0 (c, ann) e0' -> rec_red e1 (c,ann) e1' -> 
                 (forall p, p \notin [:: p0;p1] ->  d.[? p] = d'.[? p]) ->
                 ctx_red d (Action p0 p1 c, ann) d'.



Lemma end_no_ptcp : forall p,  ~ part_of SGEnd p.
Proof.
intros. move => H. inversion H.
Qed.




Definition ptcp_of_act a := let : Action p0 p1 _ := a in p0::p1::nil.

(*Fixpoint ptcps_of_g (g : gType) := 
match g with 
| GMsg a _ g0 => (ptcp_of_act a)++(ptcps_of_g g0)
| GBranch a gs => (ptcp_of_act a)++flatten (map ptcps_of_g gs)
| GRec g0 => ptcps_of_g g0
| _ => nil
end.

Lemma ptcp_in_action : forall p a,  p \in ptcp_of_act a = in_action p a.
Proof.
intros. case : a. intros. by  rewrite /= !inE.
Qed.*)


Lemma msg_cont_proj : forall a p u g e, (ptcp_from a) <> (ptcp_to a) -> co_proj (SGMsg a u g) p e -> exists e', (if p == (ptcp_from a) then e = SEMsg Sd (action_ch a) u e' else if p == (ptcp_to a) then e = SEMsg Rd (action_ch a) u e' else e = e')  /\ co_proj g p e'.
Proof.
intros.  punfold H0. inversion H0;subst.    
- rewrite /= eqxx. inversion H6. exists e0. split. done. auto. done.
- rewrite eqxx.  case : (eqVneq p p2) H6 H. move => ->. done. intros. inversion H6. eauto. done. 
- exists e. destruct a. simpl in H6. move : H6. move/negP.  rewrite negb_or. move/andP=>[]. rewrite -!eqbF_neg. move/eqP=>-> /eqP=> ->. 
  inversion H7. eauto. done.
- exists SEEnd. have : ~ in_action p a. move => H2. apply H1. auto. 
  destruct a. simpl. move/negP. rewrite negb_or. move /andP=>[].  rewrite -!eqbF_neg. move /eqP=>-> /eqP ->. 
  split;auto. pfold. apply cp_notin. move => H2. apply H1.  apply po_msg2. auto.  
Qed.

Lemma msg_cont_other : forall p p1 p2 c0 u g0 e_big, p1 <> p2 -> p \notin [:: p1; p2] -> co_proj (SGMsg (Action p1 p2 c0) u g0) p e_big ->  co_proj g0 p e_big.
Proof.
intros. have : ptcp_from (Action p2 p3 c0) <> ptcp_to (Action p2 p3 c0). done. intros.
move : (msg_cont_proj x H1)=> [] e'. move : H0. rewrite /= !inE negb_or. move/andP=>[]. rewrite -!eqbF_neg. repeat move/eqP=>->.
by move=> [] ->.
Qed.

Lemma part_of_from : forall p p2 c0 u g0 , part_of (SGMsg (Action p p2 c0) u g0) p.
Proof.
intros. constructor. by rewrite /= eqxx. 
Qed.


Lemma part_of_to : forall p p2 c0 u g0 , part_of (SGMsg (Action p p2 c0) u g0) p2.
Proof.
intros. constructor. by rewrite /= eqxx orbC. 
Qed.

Hint Resolve part_of_from part_of_to.


(*Fixpoint all_ind_g (P : action -> bool) g := 
match g with 
| GEnd => true 
| GMsg a u g0 => P a && all_ind_g P g0
| GBranch a gs => P a && all (all_ind_g P) gs 
| GRec g => all_ind_g P g
| GVar _ => true 
end.

Inductive all_g (R : (action -> Prop) -> sgType -> Prop) (P0 : action -> Prop) : sgType -> Prop :=
| all_end : all_g R P0 SGEnd
| all_msg a u g0 : R P0 g0 -> P0 a -> all_g R P0 (SGMsg a u g0)
| all_branch a gs : Forall (R P0) gs -> all_g R P0 (SGBranch a gs).*)





Lemma part_of_or : forall g p, (part_of g p) \/ (~ part_of g p).
Proof. 
Admitted.


Lemma non_refl_msg : forall p p2 c0 u g0, paco1 non_refl bot1 (SGMsg (Action p p2 c0) u g0) -> p <> p2.
Proof.
intros. punfold H. inversion H. subst. simpl in H2. done.
Qed.


Lemma sg_to_se : forall g l g' d d',  step g l g'  -> 
Coherent g -> is_full_proj d g (fun p => part_of g p) -> 
 is_full_proj d' g' (fun p => part_of g p) -> ctx_red d (label_change l) d'.
Proof.
move => g l g' d d'. elim/step_ind; intros; rewrite /=.
- unfold Coherent in H. destruct H,H2. case : a H H0 H1 H2 H3.  intros. move : (H2 p)  (H2 p2)=> [] ef Hf [] et Ht.
  have : ptcp_from (Action p p2 c0) <> (ptcp_to (Action p p2 c0)). punfold H3.  inversion H3. by simpl in*. intros. 
  move : (msg_cont_proj x Hf). rewrite /= eqxx. move => [] ef' [] Hef' Hprojef'.
  move : (msg_cont_proj x Ht). rewrite /= eqxx. have : p2 == p = false. simpl in x.  apply/eqP. 
  move => HH. apply x. subst. done. move=>->. move => [] et' [] Het' Hprojet. unfold is_full_proj in *.
  destruct H0,H1.  
  eapply ctx_red_comm with (e0:= ef)(e1:=et)(e0':= ef')(e1':=et');subst;auto.  
  rewrite /=.  intros.  move : (part_of_or (SGMsg (Action p p2 c0) u g0) p3)=>[ HH | HH].
 * move : (H2 p3)=> [] e_big eProj. erewrite H0. erewrite H1. f_equal. done. 
   apply : msg_cont_other. 2: { apply : H6. }. 
   apply : non_refl_msg. apply : H3.  apply eProj. done.  done.
 * intros.  rewrite H4 //= H5 //=. 
- unfold Coherent in H0. destruct H0, H3. case : a H H0 H1 H2 H3 H4.  intros. move : (H3 p)  (H3 p2)=> [] ef Hf [] et Ht.
  have : ptcp_from (Action p p2 c0) <> (ptcp_to (Action p p2 c0)). punfold H4.  inversion H4. by simpl in*. intros. 
  move : (msg_cont_proj x Hf). rewrite /= eqxx. move => [] ef' [] Hef' Hprojef'.
  move : (msg_cont_proj x Ht). rewrite /= eqxx. have : p2 == p = false. simpl in x.  apply/eqP. 
  move => HH. apply x. subst. done. move=>->. move => [] et' [] Het' Hprojet. unfold is_full_proj in *.
  destruct H0,H1.  
  eapply ctx_red_comm with (e0:= ef)(e1:=et)(e0':= ef')(e1':=et');subst;auto.  
  rewrite /=.  intros.  move : (part_of_or (SGMsg (Action p p2 c0) u g0) p3)=>[ HH | HH].
 * move : (H2 p3)=> [] e_big eProj. erewrite H0. erewrite H1. f_equal. done. 
   apply : msg_cont_other. 2: { apply : H6. }. 
   apply : non_refl_msg. apply : H3.  apply eProj. done.  done.
 * intros.  rewrite H4 //= H5 //=. 
Admitted.


Lemma Unroll_contractive : forall g gs, GUnroll g gs -> contractive g.
Proof.
move => g gs. unfold GUnroll. intros. punfold SH. UnUnU move : H. elim/SUnravel_ind2. induction H;auto. elim.

Lemma step_goal : forall g  gs gs' l,  step gs l gs'  -> GUnroll g gs -> exists g', GUnroll g' gs' /\ stepi g l g'.
Proof.
move => g g' gs gs'. elim. 
- intros. unfold GUnroll in H. punfold H. remember (mu_height g). elim : n  g Heqn H. 
 * intros. inversion H;subst. exists g1. split.  pfold. done. done. done. 
 * intros. inversion H0;subst. exists g1. split. done. done. 
  simpl in Heqn. inversion Heqn. pclearbot. punfold H1. rewrite -(@mu_height_subst g1 (GRec g1) 0) in H3.  move : (H _ H3 H1)=> [] g'' []. intros. exists g''. split. done.  apply GRI_rec. done.  Print contractive_i. done.
  intros. subst. pclearbot. apply H2. induction H. 
 * 
unfold GUnroll.  elim. 
- intros. punfold H. inversion H;subst. 
 * H0 H1. intros. induction H.  elim : H. 
- intros.
unfold GUnroll. intros. split. intros. induction H1. 
-
punfold H. elim : H.
- intros. inversion H.
- intros.
Lemma step_spec : forall gs l gs', step gs l gs' -> exists g g', GUnroll g gs /\ GUnroll g' gs' /\ step gs l gs'.


Lemma stepi_spec : forall g l g', stepi g l g' -> exists gs gs', GUnroll g gs /\ GUnroll g' gs' /\ step gs l gs'.
Proof.
move => g l g'.  elim. 
- intros. rewrite /GUnroll in H,H0.  punfold H. inversion H. subst. punfold H0.  apply/unroll_uniq. apply : H5. apply : H0. done. inversion H5;subst. 
intros. elim : H.
- intros.
(*Error in endpoint type, used mysort instead of value*)


Print ptcp.
Check obind. Check ESelect. Check EReceive. Check ERec. Check nth. Check map.
Fixpoint project n (g : gType) {struct g} :  endpoint :=
match g with 
| GEnd => EEnd
| GMsg (Action (Ptcp n0) (Ptcp n1) c) u g0 => if n0 == n then ESend c u (project n g0)
                                             else if n1 == n then EReceive c u (project n g0)
                                             else project n g0
| GBranch (Action (Ptcp n0) (Ptcp n1) c) gs =>if n0 == n then ESelect c (map (project n) gs)
                                             else if n1 == n then EBranch c (map (project  n) gs)
                                             else match gs with | nil => EEnd | g'::_ => project n g' end
| GVar n => EVar n
| GRec g0 => match project n g0 with 
            | EEnd => EEnd 
            | e0 => ERec e0
            end
end.
Locate flat_map.


Definition pid g := undup (ptcps_of_g g).
 Check filter.

Definition same_projection_aux n gs := exists e, Forall (fun g => project n g = e) gs.


Fixpoint Forall' {A : Type} (P : A -> Prop) l : Prop  :=
match l with 
| nil => True 
| a::l' => P a /\ (Forall' P l')
end.


Fixpoint same_proj g {struct g} :=
let fix proj_aux gs :=  
match gs with 
| nil => True 
| a::l' => same_proj a /\ (proj_aux l')
end in
match g with 
| GMsg _ _ g0 => same_proj g0
| GBranch a gs => (forall n, n \notin (ptcps_of_act a) -> exists e,  Forall' (fun g => project n g = e) gs) /\ proj_aux gs
| GRec g0 => same_proj g0
| _ => True
end.

Fixpoint acts_of_g g := 
match g with 
| GMsg a _ g0 => a::(acts_of_g g0)
| GBranch a gs => a::(flatten (map acts_of_g gs))
| GRec g => acts_of_g g 
| _ => nil
end.

Definition no_refl_action g := forall a, a \in (acts_of_g g) -> ptcp_from a != ptcp_to a.

Definition coherent g := no_refl_action g /\ same_proj g /\ (exists sg, GUnroll g sg /\ Linear sg). (*Maybe more requirements, boundness/contractiveness? No, that is implicit in the fact that g can be unrolled to sg*)

(*Next steps continue p.23*)

(*Not guarded co-recursive call, consequence of deletion in projection*)
(*CoFixpoint project (sg : sgType) (n : nat) :  seType :=
match sg with 
| SGEnd => SEEnd
| SGMsg (Action (Ptcp n0) (Ptcp n1) c) u g0 => if n0 == n then (SEMsg Sd c u (project g0 n))
                                              else if n1 == n then (SERec c u (project g0 n))
                                              else project g0 n
| _ => SBot
end.*)






















(*represent local type semantics using sets of local types and sets of queues*)


(*
Definition project2_forall (A B: Type) (R : A -> B -> Type) (l0 : seq A) (l1 : seq B) (H : Forall2 R l0 l1) :=
match H with
| Forall2_nil=> nil
| Forall2_cons _ G _ GS _ _ => G::GS
end.


Fixpoint G_of_step sg l sg'  (H : step sg l sg') : sgType  := 
match H with 
| GR1 a u _ => SGMsg a u SGEnd
| GR2 a n _ _ _ => SGBranch a nil
| GR3 a u _ _ _ H' _ => SGMsg a u (G_of_step H')
| GR4 a _ gs _ H' _  => SGBranch a (project2_forall H')
end.

Check stepG_ind.
 



Fixpoint trace_of_step sg l sg'  (H : step sg l sg') : seq (seq label) := 
match H with 
| GR1 a u _ => [::[::LU a u]]
| GR2 a n _ _ _ => [::[::LN a n]]
| GR3 a u _ _ _ H' _ => map (cons (LU a u)) (trace_of_step H')
| GR4 a _ gs _ _ _ _ _ H' _  => flatten (mkseq (fun i => map (cons (LN a i)) (trace_of_step (H' i))) (size gs))
end.

Fixpoint reduce (ls : seq label) (sg : sgType)  {struct ls} : option sgType :=
match sg,ls with 
| _,nil => Some sg
| SGMsg a u sg', (LU a' u')::nil => if (a == a') && (u == u') then Some sg' else None
| SGBranch a sgs, (LN a' n)::nil => if (a == a') then nth_error sgs n else None
| SGMsg a u sg', (LU a' u')::ls' => if (a == a') && (u == u') then match reduce ls' sg' with
                                                                  | Some sg'' => Some (SGMsg a u sg'')
                                                                  | None => None
                                                                 end
                                                             else None
| SGBranch a sgs, (LN a' n)::ls' => if a == a' then match nth_error sgs n with 
                                                   | Some sg' => match reduce ls' sg' with
                                                                 | Some sg'' => Some (SGBranch a (set_nth SGEnd sgs n sg''))
                                                                 | None => None
                                                                 end
                                                   |  None => None
                                                   end
                                              else None
| _,_ => None
end.
Check foldr.
Definition rreduce lls sg := foldr (fun t r => obind (reduce t) r  ) (Some sg) lls.

(*Fixpoint repeat_reduce lls sg :=
match lls with 
 | nil => Some sg
 | ls::lls' => match reduce ls sg with 
             | Some sg' => repeat_reduce lls' sg' 
             | None => None 
             end
end.*)

Definition wf_actions ls :=
match ls with
| nil => true 
| l::ls' => let receivers := map ptcp_to (belast l ls')
          in all (fun r => ~~(in_action r (last l ls'))) receivers
end.

Lemma wf_actions_cons : forall aa a,  ~~(in_action (ptcp_to a) (last a aa)) ->  wf_actions aa -> wf_actions (a::aa).
Proof.
elim. 
- move => a. rewrite /=. done. 
- move => a l IH a0.  rewrite /=. intros. apply/andP. split. done. done. 
Qed.


Definition wf_labels ls := wf_actions (map act_of_label ls).

Lemma wf_labels_cons : forall l0 l1 ls,  ptcp_to (act_of_label l0) \notin last l1 ls ->  wf_labels (l1::ls) -> wf_labels (l0::l1::ls).
Proof. Admitted.


Lemma step_reduce_aux : forall lls a u g , rreduce (map (fun ls => (LU a u) :: ls) lls) (SGMsg a u g) = omap (SGMsg a u) (rreduce lls g).
Proof. Admitted.

Lemma step_reduce_branch : forall lls a gs n d, n < size gs -> rreduce (map (cons (LN a n)) lls) (SGBranch a gs) = omap (fun g' => SGBranch a (set_nth d gs n g')) (rreduce lls (nth d gs n)).
Proof. Admitted.


Lemma nth_error_zip : forall (gs gs' : seq sgType) (P : sgType -> sgType -> Prop), (forall i g g',
       nth_error gs i = Some g ->
       nth_error gs' i = Some g' -> P g g')  -> Forall2 P gs gs'.
Proof. Admitted.

Lemma repeat_reduce_app :  forall lls0 lls1 sg, rreduce (lls0 ++ lls1) sg = obind (rreduce lls1) (rreduce lls0 sg).
Proof. Admitted.

Lemma step_reduce : forall sg l sg' (H : step sg l sg'), rreduce (trace_of_step H) sg = Some sg'.
Proof. 
move => sg l sg'. elim.
- intros. by rewrite /= !eqxx /=. 
- intros. by rewrite /= !eqxx /= e. 
- move => a u l0 g1 g2 s H i. rewrite /=.
 by rewrite step_reduce_aux H. 
- move => a l0 gs gs' d d' Heq Hstepd IHd Hstep IH H. rewrite /= /mkseq. 

  suff: (rreduce [seq LN a i :: y | i <- iota 0 (size gs), y <- trace_of_step (Hstep i)] (SGBranch a gs) = Some (SGBranch a gs')). 

 rewrite step_reduce_branch.
  elim : gs Heq Hstep IH. 
 * case : gs'; last done. move => _ Hstep Hrec. rewrite /=. done. 
 * move => a1 l1 IH. case : gs' IH ;first done.
   move => a2 l2 IH. case. intros.  rewrite /=. 
   rewrite repeat_reduce_app. rewrite step_reduce_branch.  
   move : (IH0 0). rewrite /=. move => ->. rewrite /=.
 move : (nth_error_zip IH). 
  clear IH. rewrite {1}/reduce_prop.  elim : gs gs' Heq Hstep. 
 * case; last done. rewrite /=. move => _ H. 
   rewrite /reduce_prop. move => _. exists nil. rewrite /=. split;auto. split;auto.
   move => ls. rewrite in_nil. done.
 * move => sg0 sgs0 IH []. rewrite /=.  done.
   move => sg1 sgs1. rewrite /=. case. move => Heq Hstep [] Hred_top Hred_rest. 
   rewrite /reduce_prop.
   intros.  move => Print List.Forall. rewrite /List.Forall.
 elim :  Search nth_error.


Definition reduce_prop l sg sg' := exists lls, repeat_reduce lls sg = Some sg' /\ all wf_labels lls /\ (forall ls, ls \in lls -> exists l' ls', ls = l'::ls' /\ last l' ls' = l).

Lemma step_reduce : forall sg l sg', step sg l sg' -> reduce_prop l sg sg'.
Proof. 
move => sg l sg'. elim.
- intros. exists ([::[::(LU a u)]]). rewrite /= !eqxx /=. split;auto. split;auto.
  move => ls. rewrite inE. move/eqP => [] ->. exists (LU a u). exists nil. auto.
- intros. exists ([::[::(LN a n)]]). rewrite /= eqxx /=. rewrite H. split; auto. split;auto.
  move => ls.  rewrite inE. move/eqP => [] ->. exists (LN a n). exists nil. auto.
- move => g1 l0 g2 a u H [] lls [] H1 [] H2 H3 H4. 
  exists (map (fun ls => (LU a u)::ls) lls). split.
 * rewrite step_reduce_aux. rewrite H1. done.   
 * split. 
  ** apply/allP. move => a_ls Hin. move : (mapP Hin)=> [] ls Hin2. 
     case : a_ls Hin. done. move => a0 ls' Hin. case. move => -> ->. 
     case : ls Hin2. done. move => a1 l1 Hin2. apply wf_labels_cons. rewrite /=. 
     move : (H3 _ Hin2) => [] l' [] ls'' [] [] -> -> ->. done. 
     apply/(allP H2). done.
  ** move => ls /mapP. move => [] ls' Hin'. case : (H3 _ Hin') => x [] ls'' [] ->. 
     exists (LU a u). exists (x::ls''). split;auto. 
- move => a l0 gs gs' Heq Hstep IH Hrec. move : (nth_error_zip IH). 
  clear IH. rewrite {1}/reduce_prop.  elim : gs gs' Heq Hstep. 
 * case; last done. rewrite /=. move => _ H. 
   rewrite /reduce_prop. move => _. exists nil. rewrite /=. split;auto. split;auto.
   move => ls. rewrite in_nil. done.
 * move => sg0 sgs0 IH []. rewrite /=.  done.
   move => sg1 sgs1. rewrite /=. case. move => Heq Hstep [] Hred_top Hred_rest. 
   rewrite /reduce_prop.
   intros.  move => Print List.Forall. rewrite /List.Forall.
 elim :  Search nth_error.


Lemma step_reduce : forall sg l sg', step sg l sg' -> exists lls, repeat_reduce lls sg = Some sg' /\ all wf_labels lls /\ (forall ls, ls \in lls -> exists l' ls', ls = l'::ls' /\ last l' ls' = l).  
Proof. 
move => sg l sg'. elim.
- intros. exists ([::[::(LU a u)]]). rewrite /= !eqxx /=. split;auto. split;auto.
  move => ls. rewrite inE. move/eqP => [] ->. exists (LU a u). exists nil. auto.
- intros. exists ([::[::(LN a n)]]). rewrite /= eqxx /=. rewrite H. split; auto. split;auto.
  move => ls.  rewrite inE. move/eqP => [] ->. exists (LN a n). exists nil. auto.
- move => g1 l0 g2 a u H [] lls [] H1 [] H2 H3 H4. 
  exists (map (fun ls => (LU a u)::ls) lls). split.
 * rewrite step_reduce_aux. rewrite H1. done.   
 * split. 
  ** apply/allP. move => a_ls Hin. move : (mapP Hin)=> [] ls Hin2. 
     case : a_ls Hin. done. move => a0 ls' Hin. case. move => -> ->. 
     case : ls Hin2. done. move => a1 l1 Hin2. apply wf_labels_cons. rewrite /=. 
     move : (H3 _ Hin2) => [] l' [] ls'' [] [] -> -> ->. done. 
     apply/(allP H2). done.
  ** move => ls /mapP. move => [] ls' Hin'. case : (H3 _ Hin') => x [] ls'' [] ->. 
     exists (LU a u). exists (x::ls''). split;auto. 
- move => a l0 gs gs' g g' Hstep IH Hrec. move : (nth_error_zip IH). 
 elim :  Search nth_error.


Lemma linear_reduce : forall sg ls sg', Linear sg -> reduce sg ls = Some sg' -> wf_labels ls -> Linear sg'.
Proof. Admitted.

Lemma linear_repeat_reduce_cons : forall l sg sg' a,  repeat_reduce (a :: l) sg = Some sg' -> exists sg'', reduce sg a = Some sg'' /\ repeat_reduce l sg'' = Some sg'.
Proof.
move => l sg sg' a.  rewrite /=. destruct (reduce sg a). intros. exists s. auto.
done. 
Qed.

Lemma linear_repeat_reduce : forall lls sg sg', Linear sg -> repeat_reduce sg lls = Some sg' -> all wf_labels lls -> Linear sg'.
Proof. 
elim. 
- rewrite /=. intros. injection H0. move=><-. done. 
- intros. move : (linear_repeat_reduce_cons H1)=> [] x []. intros. move : H2.  rewrite /=. move/andP=>[]. intros. move : (linear_reduce H0 a0 a1). intros. apply :H. apply linear_reduce0. apply b. apply b0. 
Qed.

Lemma linear_step : forall sg l sg', step sg l sg' -> Linear sg -> Linear sg'.
Proof. 
intros.  move : (step_reduce H) =>[] x [H2 H3]. apply/linear_repeat_reduce.  apply H0. apply H2. 
apply H3. 
Qed.







Fixpoint end_list sgs :=
match sgs with 
| nil => true 
| GEnd::sgs' => end_list sgs'
| _::sgs' => false
end.

Fixpoint reduce (sg : sgType) (g : gType) {struct g} :=
let fix reduce_list sgs gs {struct gs} := 
match sgs,gs with 
 | nil,nil => Some nil
 | sg::sgs',g::gs' =>  obind (fun sgs'' => omap (fun sg' => sg'::sgs'' )  (reduce sg g)) (reduce_list sgs' gs')
 | _,_ => None 
end
in
match sg , g with 
| _,GEnd => Some sg
| SGMsg a u sg, GMsg a' u' GEnd => if (a == a') && (u == u') then Some sg else None
| SGMsg a u sg, GMsg a' u' g' => if (a == a') && (u == u') then omap (fun sg' => SGMsg a u sg') (reduce sg g') else None
| SGBranch a sgs, GBranch a' gs  => if a == a' then 
                                    if end_list gs then nth_error sgs (size gs)
                                                   else omap (fun sgs' => SGBranch a sgs') (reduce_list sgs gs) 
                                  else None
| _,_ => None
end.

(*receiver constranint boolean predicate on labels
 main lemma. if there is a normal reduction, there exists indcutive global types with receiver constraint s.t we can do the same reduction. By linearity and receiver constraint on this label, we know its leaves aren't used in any in/output chains. Next steps?
 A sub type relation. The bigger type contains all paths that are in the smaller type
 Define next as a partial function, next g a i, nexts g ais

 How do I connect all this to acturaly show the reduced G is linear?
 we can do the same red*)



(*Change ≺ to sequence of labels. Normal reduction implies a sequence of computation reductions that each have receiver constraint. Suffices to show that such a computation reduction preserves chains. Only affected chains are prefixes of ≺ sequence. If reduction sequence = ≺ sequence, the channel condition doesn't hold. If reduction sequence is a prefix, there exists a bitmask such that ≺ sequence such that chains are preserved *)
Lemma red_lin : forall g g_l g', Linear g -> reduce g g_l = Some g' -> Linear g'.
Proof. Admitted.





(*Besides well formedness we can also define input dependency and output dependency on rose trees
 and transform the tricky statement about k <> k' in the proof to there not existing any input or output dependency
 in the well formed rose tree that was used to reduce with because of the receiver criteria*)
Inductive wf_r (A : Type) : rose A -> A -> Prop :=
| wf_r0 a : wf_r (Rose a nil) a
| wf_r1 rs a1 a : (forall r, In r rs -> wf_r r a1) ->  wf_r (Rose a rs) a1.

Check nth_error.

Inductive reduce : sgType -> rose label -> sgType -> Prop :=
| SGMsg0 a u g0 : reduce (SGMsg a u g0) (Rose (LU a u) nil) g0
| SGMsg1 a u g0 g0' r' : reduce g0 r' g0' -> reduce (SGMsg a u g0) (Rose (LU a u) ([::r'])) (SGMsg a u g0')
| SGBranch0 a n g0 gs g: List.nth_error gs n = Some g -> reduce (SGBranch a gs) (Rose (LN a n) nil) g0
| SGBranch1 a a' rs gs  gs' n g r g' : (forall r, In r rs -> wf_r r a')  ->  (forall i, nth_error gs i = Some g -> nth_error rs i = Some r -> nth_error gs' i = Some g' -> reduce g r g' ) -> reduce (SGBranch a gs) (Rose (LN a n) rs) (SGBranch a gs').



Fixpoint reduce (g : sgType) (r : rose label) :=
match g,r with 
| SGMsg a u g0, Rose (LU a' u') nil => if a == a' && u == u' then Some g0 else None
| SGMsg a u g0, Rose (LU a' u') ([r']) => if a == a' && u == u' then omap (fun g' => SGMsg a u g') (reduce g0 r')
| SGBranch a gs, Rose (LN a' n) nil => if a == a' then List.nth_error gs n
| SGBranch a gs, Rose (LN a' n) rs => if a == a' && leq (size gs) (size rs) then 

*)


(*fix async definitions*)
(*Inductive EnvStep2 : env -> label -> env -> Prop := 
| envstep2_msg (Δ: env) p0 p1 e0 e1 c v : Δ.[? p0] = Some e0 -> Δ.[? p1] = Some e1 -> EnvStep2 Δ.[p0 <- SEMsg Sd c v e0].[p1 <- SEMsg Rd c v e1] (to_label (inl v) p0 p1 c) Δ
| envstep2_msg_async (Δ Δ': env) p0 p1 e0 e1 e0' e1' c v a : Δ.[? p0] = Some e0  ->  Δ.[? p1] = Some e1 ->  Δ'.[? p0] = Some e0' -> Δ'.[? p1] = Some e1' -> ~~(in_action p1 a) -> EnvStep2 Δ (LU a v) Δ' -> action_ch a <> c ->  EnvStep2 Δ.[p0 <- SEMsg Sd c v e0].[p1 <- SEMsg Rd c v e1] (LU a v) Δ'.[p0 <- SEMsg Sd c v e0'].[p1 <- SEMsg Rd c v e1']
| envstep2_branch (Δ : env) (Δs : seq env) p0 p1 es0 es1 c n : n < size Δs -> 
                                                               Forall2 (fun (d : env) e => d.[? p0] = Some e) Δs es0 -> 
                                                               Forall2 (fun (d : env) e => d.[? p1] = Some e) Δs es1 -> 
                                                               Forall (fun d => d.[~ p0].[~ p1] = Δ) Δs ->
                                                               EnvStep2 Δ.[p0 <- SEBranch Sd c es0].[p1 <- SEBranch Rd c es1] (to_label (inr n) p0 p1 c) 
                                                                       (nth [fmap] Δs n).
| envstep2_branch_async (Δ : env) (Δs : seq env) p0 p1 es0 es1 c n : n < size Δs -> 
                                                               Forall2 (fun (d : env) e => d.[? p0] = Some e) Δs es0 -> 
                                                               Forall2 (fun (d : env) e => d.[? p1] = Some e) Δs es1 -> 
                                                               Forall (fun d => d.[~ p0].[~ p1] = Δ) Δs ->
                                                               Forall2 (fun d0 d1 => EnvStep2 d0 (LN a n) d1) Δs Δs' ->
                                                               Forall2 (fun (d : env) e => d.[? p0] = Some e) Δs' es0' -> 
                                                               Forall (fun d => d.[~ p0].[~ p1] = Δ') Δs' ->
                                                               EnvStep2 Δ.[p0 <- SEBranch Sd c es0].[p1 <- SEBranch Rd c es1] (LN a n)
                                                                        Δ'.[p0 <- SEBranch Sd c es0'].[p1 <- SEBranch Rd c es1]. *)



(*Inductive Ecomm : env -> label -> env -> Prop := 
| Ecomm_rule p0 p1 (Δ : env) e0 e1 e0' e1' c vn : Estep e0 (Sd,c,vn) e0' -> Estep e1 (Rd,c,vn) e1' ->
                                                  Ecomm Δ.[ p0 <- e0].[p1 <- e1] (to_label vn p0 p1 c) ((Δ.[p0 <- e0']).[p1 <- e1']).*)


(*Definition get (Δ : env) (p : ptcp) := 
if Δ.[? p] is Some e then  e else SEEnd. 

Definition gets (Δs : seq env) (p : ptcp) := map (fun Δ => get Δ p ) Δs.


(*Bake property into inductive definition even though it should be provable, not obious how because of coinduction*)
Definition no_end (d : env) := forall p e, d.[? p] = Some e -> e <> SEEnd.*)




(*Lemma allproj_no_ends : forall g d, co_allproj g d -> no_end d.
Proof.
intros. punfold H. induction H; rewrite /no_end;intros.  rewrite fnd_fmap0 in H. done. 
move : H1.
rewrite fnd_set. destruct (p == p1) eqn:Heqn. case. intros. subst. done.
rewrite fnd_set. destruct (p == p0) eqn:Heqn1. case. move=> <-. done. move : H. rewrite /no_end. intros. eauto. 
move : H2.
rewrite fnd_set. destruct (p == p1) eqn:Heqn. case. intros. subst. done.
rewrite fnd_set. destruct (p == p0) eqn:Heqn1. case. move=> <-. done. move : H. rewrite /no_end. intros. eauto. 
Qed.*)
