From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import finmap.
From Paco Require Import paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Export NewSyntax  Bisimulation Projection Inductive_Linearity Structures.

Let inE :=  NewSyntax.inE.


Unset Elimination Schemes. Check epred.
Inductive Estep : endpoint ->  (dir * ch * (value + nat))  -> endpoint -> Prop :=
| estep_msg d c v e0  : epred (EMsg d c v e0) -> Estep (EMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d d2 vn c c' v e0 e0'  : epred (EMsg d c' v e0) -> (d = Sd \/ d2 = Sd) -> Estep e0 (d2,c,vn) e0' -> c <> c' -> 
                                        Estep (EMsg d c' v e0) (d2,c,vn) (EMsg d c' v e0')
| estep_branch n es d c   : epred (EBranch d c es) ->  n < size es -> Estep (EBranch d c es) (d,c, inr n) (nth EEnd es n)
| estep_branch_async es0 es1 vn d d2 c c'  : epred (EBranch d c' es0) -> (d = Sd \/ d2 = Sd) -> size es0 = size es1 -> Forall (fun p =>  Estep p.1 (d2,c,vn) p.2) (zip es0 es1) -> c <> c' -> 
                                          Estep (EBranch d c' es0) (d2,c,vn) (EBranch d c' es1)
| estep_rec e l e1 e' : epred e -> epred e1 ->  ebisimilar e e1 -> Estep e1 l e' -> Estep e l e'.
Set Elimination Schemes.
Hint Constructors Estep.


Lemma Estep_ind
     : forall P : endpoint -> dir * ch * (value + nat) -> endpoint -> Prop,
       (forall (d : dir) (c : ch) (v : value) (e0 : endpoint), epred (EMsg d c v e0) ->  P (EMsg d c v e0) (d, c, inl v) e0) ->
       (forall (d d2 : dir) (vn : value + nat) (c c' : ch) (v : value) (e0 e0' : endpoint), epred (EMsg d c' v e0) -> (d = Sd \/ d2 = Sd) ->
        Estep e0 (d2, c, vn) e0' -> P e0 (d2, c, vn) e0' -> c <> c' -> P (EMsg d c' v e0) (d2, c, vn) (EMsg d c' v e0')) ->
       (forall (n : nat) (es : seq endpoint) (d : dir) (c : ch),  epred (EBranch d c es) ->  n < size es -> P (EBranch d c es) (d, c, inr n) (nth EEnd es n)) ->
       (forall (es0 es1 : seq endpoint) (vn : value + nat ) (d d2 : dir) (c c' : ch), (d = Sd \/ d2 = Sd) -> epred (EBranch d c' es0) ->
        size es0 = size es1 ->
        Forall (fun p : endpoint * endpoint => Estep p.1 (d2, c, vn) p.2) (zip es0 es1) ->
        Forall (fun p : endpoint * endpoint => P p.1 (d2, c, vn) p.2) (zip es0 es1) ->
        c <> c' -> P (EBranch d c' es0) (d2, c, vn) (EBranch d c' es1)) ->
       (forall (e : endpoint) (l : dir * ch * (value + nat) ) (e1 e' : endpoint), epred  e -> epred e1 ->
        ebisimilar e e1 -> P e1 l e' -> P e l e') ->
       forall (e : endpoint) (p : dir * ch * (value + nat)) (e0 : endpoint), Estep e p e0 -> P e p e0.
Proof.
intros. move : e p e0 H4. fix IH 4;intros. destruct H4.
- apply H;auto.
- apply H0;auto.
- apply H1;auto.
- apply H2;auto. elim : H7;auto. 
- eapply H3; eauto. 
Qed.



(*Lemma Estep_cont : forall e0 l e1, Estep e0 l e1 -> econtractive2 e0.
Proof.
move => e0 l e1. elim;try done;intros. simpl. move : H2.  move/forallzipP=>/=H'. apply/allP=>x /nthP=>Hn. specialize Hn with EEnd. destruct Hn. rewrite -H4.  apply : H'. repeat constructor. done. done.
Qed.

Lemma Estep_cont2 : forall e0 l e1, Estep e0 l e1 -> econtractive2 e1.
Proof.
move => e0 l e1. elim;try done;intros. apply (allP H). cc. simpl. move : H2.  move/forallzipP=>/=H'. apply/allP=>x /nthP=>Hn. specialize Hn with EEnd. destruct Hn. rewrite -H4.  apply : H'. repeat constructor. done. rewrite H0. done.
Qed.*)


Inductive EnvStep : env -> label -> env -> Prop := 
| envstep_rule (Δ Δ' : env) e0 e1 e0' e1' l : Estep e0 (Sd,action_ch l.1,l.2) e0' ->  Estep e1 (Rd,action_ch l.1,l.2) e1' ->  
                           domf Δ = domf Δ' -> (forall p e e',  Δ.[? p] = Some e -> Δ'.[? p] = Some e' -> ebisimilar e e') -> EnvStep Δ.[ptcp_from l.1 <- e0].[ptcp_to l.1 <- e1] l  Δ'.[ptcp_from l.1 <- e0'].[ptcp_to l.1 <- e1'].
Hint Constructors EnvStep.

Lemma mapf : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A), k \in S -> [fmap x : S => F (val x)].[? k] = Some (F k).
Proof.
intros. rewrite /=. rewrite /fnd.  case : insubP;rewrite /=;intros; subst. f_equal. rewrite ffunE. done. rewrite H in i. done. 
Qed.

Lemma mapf2 : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A), k \notin S -> [fmap x : S => F (val x)].[? k] = None.
Proof.
intros. rewrite /=. rewrite /fnd.  case : insubP;rewrite /=;intros; subst. rewrite i in H. done. done. 
Qed.

Lemma mapf_if : forall (A : choiceType) (B : Type) (S : {fset A}) (F : A -> B) (k : A),  [fmap x : S => F (val x)].[? k] = if k \in S then Some (F k) else  None.
Proof.
intros. rifliad. rewrite mapf. done. done. rewrite mapf2. done. lia. 
Qed.

Lemma fsubset_in : forall (A : choiceType) (b c : {fset A}), b `<=` c -> (forall j, j \in b -> j \in c).
Proof.
intros. Search _ fsub1set. move : H0. rewrite -!fsub1set.  intros. apply : fsubset_trans. apply : H0. apply H. 
Qed. 


(*Definition try_fnd (d : env) (p : ptcp) := if d.[? p] is Some e then e else EEnd.*)

(*Definition map_subst (i : nat) (d : env) g := [fmap x : (domf d) => (try_fnd d (val x))[s (project g (val x))//i]]. *)


(*Lemma ptcps_subsitution_aux : forall g0 g1 i, ptcps_of_g g0 `<=` ptcps_of_g (substitution i g0 g1).
Proof. elim;rewrite /=;try done;intros. rifliad. simpl. done. apply/fsetUSS.  done. eauto. 
rewrite !big_map. apply/fsetUSS. done. apply/bigfcupsP. intros.  apply/fsubset_trans. apply : (H i0 H0). 
3 : { apply/bigfcup_sup. done. done. }
Qed.

Lemma ptcps_subsitution_aux1 : forall g0 g1 i, ptcps_of_g (substitution i g0 g1) `<=` ptcps_of_g g0 `|` (ptcps_of_g g1).
Proof. elim;rewrite /=;try done;intros. rifliad. Search _ (fset0 `|`_).  rewrite fset0U. done. rewrite /=. done.
rifliad. simpl. Search _ (?a `<=` ?a `|` _). apply fsubsetUl. simpl. done. 
 apply/fsetUSS. rewrite fsubsetUl //=. done. done. done. rewrite -fsetUA. apply/fsetUSS. done. rewrite !big_map. apply/bigfcupsP. intros.  apply/fsubset_trans. apply : (H i0 H0). apply/fsetUSS. apply/bigfcup_sup. done. done. done. 
Qed.

(*Search _ (?A `<=` _ ->  _).
Lemma squeeze : forall (S0 S1 : ptcps), S0 `<=` S1 -> S1 `<= S2 -> *)

Lemma ptcps_substitution : forall g, ptcps_of_g g[GRec g] = g.
Proof.
intros. apply/fsetP=>k. 
apply Bool.eq_true_iff_eq. split. intros. move : (ptcps_subsitution_aux1 g (GRec g) 0). move/fsubset_in. 
have : ptcps_of_g g = ptcps_of_g (GRec g). done. move=><-. Search _ (?a`|`?a). rewrite fsetUid. move=>Hall.  apply Hall. done. 
intros. move : (ptcps_subsitution_aux g (GRec g) 0). move/fsubset_in=>Hall. apply Hall. done. 
Qed.*)




(*Lemma project_end : forall g p, p \notin (ptcps_of_g g) -> lpreds size_pred g -> project g p.
Proof.
elim;intros;rewrite /=;try done.
- eauto. eauto. 
- simpl in H0. apply H in H0. rewrite /is_leaf in H0.  destruct H0. rewrite /is_leaf H0. auto. destruct H0. rewrite H0. eauto. by simpl in H1. 
- move : H0.  rewrite /= !inE  !negb_or. rifliad. by rewrite (eqP H0) eqxx.  rewrite (eqP H2) eqxx. lia. 
  intros. destruct (andP H3). apply H in H5 as [].  auto. destruct H5. eauto. eauto. 
- move : H0. rewrite /= !inE !negb_or. rifliad. by rewrite (eqP H0) eqxx. rewrite (eqP H2) eqxx. lia.
  rewrite big_map match_n. move/andP=>[] _. move/bigfcupP=>HH.   
  have : p \notin ptcps_of_g (nth GEnd l 0). apply/negP=>HH'. apply : HH. exists (nth GEnd l 0). rewrite mem_nth //=.  
  simpl in H1. lia. done. intros. edestruct H. 2 : { apply : x. } rewrite mem_nth //=. by simpl in H1;lia. simpl in H1. 
  destruct (andP H1). apply (allP H4). rewrite mem_nth //=. rewrite H3. auto.  destruct H3. rewrite H3. eauto. 
Qed.*)





(*Lemma projmap_subst : forall g0  g i S, lpreds [::bound] g -> projmap S (g0[s g//i]) = map_subst i (projmap S g0) g.
Proof.
intros. rewrite /projmap /map_subst. apply/fmapP=>k. rewrite !mapf_if. 
rewrite (@mapf_if _ _ _ (fun x =>  (try_fnd ([fmap p => project g0 (val p)]) (x))[s (project g (x))//i])) /=.
rifliad. f_equal. rewrite project_subst. rewrite /try_fnd. rewrite mapf_if H0. done. done. 
Qed.*)



(*Lemma subst_diff : forall e0 e1 e2 k1 k2, k1 <> k2 -> e0[e e1//k1][e e2//k2] = e0[e e2//k2][e e1//k1].
Proof. Admitted.*)


(*Lemma in_subst : forall e e1 n, n \in fv e[s e1//n] = (n \in fv e) && (n \in fv e1).
Proof. elim;intros;rewrite /= ?inE.
- rifliad. rewrite eq_sym H /=. done. rewrite /= !inE eq_sym H /=. done. done.
- rifliad. rewrite !inE neg_sym H0 /=. done. rewrite /= !inE H neg_sym H0 /=. done. rewrite H. done.
- rewrite !big_map. induction l. rewrite !big_nil !inE. done. rewrite !big_cons !inE. rewrite H. rewrite IHl. destruct (n \in efv a) eqn:Heqn;rewrite Heqn /=.  
  destruct (n \in efv e1) eqn:Heqn2;rewrite Heqn2 /=. done. lia. done. intros. apply H. auto. auto. 
Qed.*)


(*Lemma double_subst : forall e0 e1 e2 k1 , e0[e e1//k1][e e2//k1] = e0[e e1//k1].
Proof. Admitted.*)



(*Lemma ueqe_fv : forall e0 e1, paco2 Unravele bot2 e0 e1 -> fv e0 = fv e1. 
Proof. 
move => e0 e1 H. punfold H. induction H; auto. ich H. auto. rs. ich H0. apply H.  2 : { auto. }induction H2;rs;auto.  ich H0. pcofix CIH. intros.
*)

Lemma bool_iff : forall (b0 b1 : bool), b0 = b1 <-> (b0 <-> b1).
Proof. move => [] [];split;auto;intros;try done. suff : false. by  move=>->. by rewrite -H. suff : false. by move=>->. rewrite H. done. 
Qed.


(*Lemma ueqe_fv2 : forall e0 e1, bisimilar e0 e1 ->  fv e0 = fv e1. 
Proof. intros. punfold H. inversion H. subst. Admitted.*)
(*
Proof. move => e0 e1 H. punfold H. induction H;auto.  intros. intros. eapply  ueqe_fv. intros. apply : H2. apply : monotone_ueqe. punfold H. intros. ich PR. apply  H. eapply Unravele_r in H. punfold H. pfold.

(*Lemma bound_ueqe : forall e0 e1, bound e0 -> e0 =f= e1*)
Lemma ueqe_fv : forall e0 e1,  fv e0 = fv e1. 
Proof. 
move => e0 e1 r H H2. induction H2; auto. rs. auto. rs. rewrite !big_map.
move : H1.  move/forallzipP=>HH. simpl in HH. intros. apply/fsetP=>k. rewrite !big_exists. rewrite bool_iff. split;intros.
destruct (hasP H3). move : H4.  move/nthP=>Hnth. specialize Hnth with EEnd. destruct Hnth. apply/hasP. exists (nth EEnd gs' x0).
 rewrite H0 in H4. cc. erewrite <- H. apply : H5. specialize HH with EEnd EEnd x0. rewrite -H6. apply  HH. done. done. 

destruct (hasP H3). move : H4.  move/nthP=>Hnth. specialize Hnth with EEnd. destruct Hnth. apply/hasP. exists (nth EEnd gs x0).
 rewrite -H0 in H4. cc. erewrite H. apply : H5. specialize HH with EEnd EEnd x0. rewrite -H6. apply  HH. done. cc. 
rs. intros. apply/fsetP=>k. rewrite !inE. apply H in H0.  rewrite -H0. rewrite fv_subst. by rewrite !inE. 
rewrite /bound in H1.  by apply/eqP. 

rs. intros. apply/fsetP=>k. rewrite !inE. apply H in H0.  rewrite H0. rewrite fv_subst. by rewrite !inE. 
rewrite /bound in H2.  by apply/eqP. 
intros. rewrite IHUnravele1 //=. rewrite IHUnravele2 //=. Admitted.*)

(*Lemma Unravele_r : forall e0 e1 r, paco2 Unravele bot2 e0 e1 -> paco2 Unravele r e0 e1.
Proof. pcofix CIH.
intros. pfold. apply : monotone_ueqe. punfold H0. intros. ich PR. right. apply CIH. done. Qed.
*)

(*Lemma ueqe_fv2 : forall e0 e1, bisimilar e0 =f= e1 ->  bound e0 -> bound e1 ->   fv e0 = fv e1. 
Proof. intros. eapply  ueqe_fv. intros. apply : H2. apply : monotone_ueqe. punfold H. intros. ich PR. apply  H. eapply Unravele_r in H. punfold H. pfold.*)
Lemma fv_eq1 : forall g p n, lpreds rec_pred g  -> n \in endpoint_fv (project g p) -> n \in gType_fv g. 
Proof. Admitted.
(*
elim;rewrite /=;rs;intros;rewrite ?inE.
- move : H0. rewrite !inE. done.
- rewrite !inE in H0. done.
- move : H1.  rifliad. rs. rewrite !inE. split_and. eapply H. cc. eauto. intros. destruct (eqVneq n0 n). subst. by rewrite H3 in H2. rewrite i /=. apply : H. cc. eauto.
-
 move : H1. rifliad. rs. intros. apply :H. cc. eauto. rs. intros. apply : H. cc. eauto. intros. apply : H. cc. eauto.
- move : H1. rifliad. rs. rewrite !big_map !big_exists. move/hasP=>[];intros. apply/hasP. exists x. done. apply : H. done. cc. eauto.
  rs. rewrite !big_map !big_exists. move/hasP=>[];intros. apply/hasP. exists x. done. apply : H. done. cc. eauto.
- rewrite match_n big_map big_exists. intros. apply/hasP. exists (nth GEnd l 0). cc. apply : H. cc. cc. eauto.
Qed.*)

(*Lemma ppred_same_vars : forall g p, lpreds rec_pred g ->  same_vars (project g p).
Proof. 
elim;rewrite//=;rs;intros. rifliad;simpl;auto. all: try apply H; cc. rifliad;simpl;auto. all : try apply H; cc.
rifliad. simpl. split_and. rewrite all_map. apply/allP=>e'. intros. simpl. erewrite nth_map. 

apply/eqP. apply/ueqe_fv2/bisimP.  split_and. *)
(*
suff : (p \in a) || bisimilar (project (nth GEnd l 0) p) (project x p).
rewrite !inE H1 /=.
apply (allP (allP H2 _ p0)). 
rewrite !inE H1 /= . rewrite big_map.
rewrite all_map. apply/allP. intro.  intros. simpl. apply H. done. cc. simpl. 
split_and. 
apply/allP=>e'. intros. move : H3. move/mapP=>[]. intros. subst.  erewrite nth_map.  
nth_lpreds 2 H0. simpl. move => HH. apply/eqP/ueqe_fv/ueqeP. split_and. cc. 
rewrite all_map. apply/allP. intro.  intros. simpl. apply H. done. cc. 
rewrite match_n. apply H. cc. cc. 
Grab Existential Variables. all: repeat constructor.
Qed.*)


(*Lemma fv_eq2 : forall g p n, lpreds (same_varsg::rec_pred) g  -> n \in gType_fv g ->  n \in endpoint_fv (project g p). 
Proof. Admitted.*)
(*elim;rewrite /=;rs;intros;rewrite ?inE.
- move : H0. rewrite !inE. done.
- rewrite !inE in H0. done.
- move : H1.  rifliad. rs. rewrite !inE. split_and. have : lpreds (same_varsg::rec_pred) g. cc. move/H=>HH. move : (HH p n0 H4). rewrite (eqP H1) !inE. lia. 
  rs. rewrite !inE. split_and. apply H. cc.  done.
- rewrite !inE. split_and. apply : H. cc.  done.
 rifliad. rs. apply : H. cc.  done. rs. apply H. cc.  done. apply H. cc. done. 
- rifliad;rs. move : H1.  rewrite !big_map !big_exists. move/hasP=>[];intros. apply/hasP. exists x. done. apply : H. done. cc.  eauto.
  move : H1.  rewrite !big_map !big_exists. move/hasP=>[];intros. apply/hasP. exists x. done. apply : H. done. cc. eauto.
- move : H1. rewrite match_n big_map big_exists. intros.
  destruct (hasP H1). move : H4. move/nthP=>Hnth. specialize Hnth with GEnd.
  move : H1. move/hasP=>[]. intros. apply : H. cc. cc. nth_lpreds 0 H0. simpl. split_and. rewrite (eqP (allP H _ p0)) //=.
Qed.
*)

(*Lemma fv_eq : forall g p, lpreds (same_varsg::rec_pred) g  -> gType_fv g = endpoint_fv (project g p).
Proof. 
intros. apply/fsetP=>k. Admitted. *)
(*destruct (k \in fv g) eqn:Heqn. rewrite fv_eq2 //=. 
destruct (k \in fv (project g p)) eqn:Heqn2. erewrite fv_eq1  in Heqn. done. cc. 
eauto. done. 
Qed.*)



(*Lemma ppred_same_varsg : forall g, lpreds rec_pred g -> same_varsg g.
Proof.  
elim;rewrite /=;rs;intros;try done. apply H. cc. apply H.  cc.
split_and. apply/allP=>e' Hin. 
erewrite !fv_eq. apply/eqP. apply/ueqe_fv. apply/ueqeP. nth_lpreds 2 H0. simpl. split_and.
cc. cc. apply/allP=>x. intros. apply H. done. cc. 
Grab Existential Variables. all : repeat constructor.
Qed.
*)

(*Lemma subst_distr : forall e e' e2 n n0, lpreds [::bound] e' ->  n<> n0 ->  fv e2 `<=` fv e ->  same_vars e -> e[s e' // n][s e2[s e' // n] // n0] = e[s e2//n0][s e' // n].  
Proof. 
elim.
- intros. simpl. rs. rifliad. by rewrite -(eqP H3)  -(eqP H4)in H0.  simpl. rs. rifliad. rewrite subst_nop.  done. nth_lpreds 0 H.  move/eqP->. by rewrite !inE.  
  rs. rewrite /= H4. done. rs. by rewrite /= H3 H4.
- intros. done. 
- intros. simpl. rs. rifliad. rs. by rewrite /= H5 H4. 
  rs. rewrite /= H5 H4.  f_equal. f_equal. rewrite (eqP H4) in H2. rewrite subst_nop. done. apply/negP=>HH.  move : (fsubset_in H2 HH). rewrite /= !inE.  split_and. 
  rs. rewrite (eqP H5) /= eqxx. rewrite -(eqP H5) H4. done. rs. rewrite /= H5 H4 /=.  f_equal.  rewrite H. done. cc. done. rs_in H2.  simpl in H2. apply/fsubsetP=>k. intros. move : (fsubset_in H2 H6). rewrite !inE. split_and. simpl in H3. done.
- intros. simpl. rs. f_equal. apply H. cc. done. done. done.  
- intros. simpl. rs. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl. apply H. done. cc. done. simpl in H2. apply/fsubsetP=>p. intros. move : (fsubset_in H2 H5).  rs.
  rewrite big_map. rewrite big_exists.  move/hasP=>[]x. intros. simpl in H3. move : p0. move/nthP=>Hnth. specialize Hnth with EEnd. destruct Hnth.
  suff : p \in fv (nth EEnd l 0). split_and. move : (allP H8 _ H4). move/eqP.   move=><-. done. rewrite -H7 in q. have : nth EEnd l x0 \in l.  cc. intros.
  split_and.  move :(allP H8 _ x1).  move/eqP. move=>->. done. simpl in H3. split_and. apply (allP H6). done. 
Qed.*)

(*Lemma double_inner_subst: forall e e' e2 n n0, lpreds [::bound] e' ->  n<> n0 ->  efv e2 `<=` efv e ->  same_vars e -> e[e e2[e e' // n] // n0][e e' // n] = e[e e2//n0][e e' // n].  
Proof. 
elim.
- intros. simpl. rifliad. rewrite double_subst. done. 
- intros. done. 
- intros. simpl. rifliad. simpl. rifliad. simpl in H2. f_equal. f_equal. rewrite (eqP H5) in H3. rewrite subst_nop. done. apply/negP=>HH.  move : (fsubset_in H2 HH). rewrite !inE.  rewrite (eqP H5) eqxx. done.  f_equal.  rewrite H. done. cc. done. simpl in H2. apply/fsubsetP=>k. intros. move : (fsubset_in H2 H6). rewrite !inE. split_and. 
- intros. simpl. f_equal. simpl in H3. done. 
- intros. simpl. f_equal. apply : H. cc. done. simpl in H2.  done. simpl in H3. done.
- intros. simpl. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl. apply H. done. cc. done. simpl in H2. apply/fsubsetP=>p. intros. move : (fsubset_in H2 H5). 
  rewrite big_map. rewrite foldr_exists.  move/hasP=>[]x. intros. simpl in H3. move : p0. move/nthP=>Hnth. specialize Hnth with EEnd. destruct Hnth.
  suff : p \in efv (nth EEnd l 0). split_and. move : (allP H8 _ H4). move/eqP.   move=><-. done. rewrite -H7 in q. have : nth EEnd l x0 \in l.  cc. intros.
  split_and.  move :(allP H8 _ x1).  move/eqP. move=>->. done. simpl in H3. split_and. apply (allP H6). done. 
Qed.*)


(*Lemma ueqe_subst : forall e0 e1 e' n, (lpreds [::bound])e' ->  e0 =f= e1 ->  e0[e e'//n] =f= e1[e e'//n].
Proof.  
elim.
3 : {  simpl.  intros. rifliad. pfold. constructor. left. rewrite (eqP H2).
- intros. simpl. rifliad. punfold H0. inversion H0. subst. simpl. rewrite H1. done. subst. simpl. rewrite eq_sym.  H1. 
pfold. constructor. right.  apply : CIH. cc. cc. 
pfold. constructor. by rewrite !size_map.
have : (zip (map (fun e0' => (e0')[e e' // n]) gs)  (map (fun e0' => (e0')[e e' // n]) gs')) = map (fun p => (p.1[e e'//n ],p.2[e e'//n])) (zip gs gs'). clear H2 CIH H H0. elim : gs gs'.  destruct gs'. done. by simpl.  destruct gs'. done.
simpl.  f_equal. apply H. move=>->. move : H2. move/forallzipP=>HH. apply/Forall_forall. simpl in HH. intros. right. 
move : H1. move/nthP=>HH'. specialize HH' with (EEnd,EEnd). destruct HH'. rewrite -H2. erewrite nth_map. simpl. apply : CIH. cc.
erewrite nth_zip. simpl. move : H1.  rewrite size_map size_zip minnE H nat_fact. intros. 
(*rewrite -H in H1.  cc.
 cc. erewrite nth_zip.  simpl. move : H2.  rewrite size_map size_zip minnE H nat_fact. intros. cc. done.
rewrite nth_zip /=. *) suff : upaco2 Unravele bot2 (nth EEnd gs x0) (nth EEnd gs' x0). case. eauto. done. apply : HH. done. rewrite H. done. done.
move : H1. by rewrite size_map size_zip minnE H nat_fact. 
rifliad. 
pfold. constructor. ich H. rewrite (eqP H1). right. 
 rewrite -(@subst_nop (g[e ERec n g // n]) e' n). apply : CIH. cc. rewrite -(eqP H1). done. 
rewrite in_subst negb_and. apply/orP. right. by rewrite /= !inE. 
ich H. pfold. constructor.  right. have : ERec n0 g[e e' // n] = (ERec n0 g)[e e' //n].  rewrite /= H1. done. move=>->. rewrite subst_distr.  
apply : CIH. cc. done.
rifliad.*)

Ltac kb d := let Heqn := fresh "Heqn" in destruct d eqn:Heqn;rewrite ?Heqn //=. 

(*TODO*)
(*Lemma ptcp_subst : forall (A : eqType) (B : choiceType)  x p g1 i (F : A -> {fset B}) , (p \in F (x)[g g1 // i]) = (p \in F x) || ((i \in fv x) && (p \in F g1)).
Proof.
elim;rewrite /=;intros.
- rifliad. by rewrite !inE (eqP H) eqxx /=. by rewrite !inE eq_sym H. by rewrite !inE. 
- rifliad. rewrite /= !inE (eqP H0) eqxx /=. lia. rewrite /= !inE. rewrite neg_sym. rewrite (negbT H0) /= H. done.
  rewrite !inE H. by rewrite orbA.  
- rewrite !big_map. rewrite !inE. kb (p == ptcp_from a). kb (p == ptcp_to a). 
  clear Heqn Heqn0. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //=. rewrite IHl. rewrite orbA. kb (p \in ptcps_of_g a0).  kb (i \in fv a0). kb (p \in ptcps_of_g g1). lia. 
  by rewrite andbC /= orbC /=.  intros. apply H. auto. 
Qed.*)


(*Lemma ptcp_subst : forall x p g1 i, (p \in ptcps_of_g (x)[s g1 // i]) = (p \in ptcps_of_g x) || ((i \in fv x) && (p \in ptcps_of_g g1)).
Proof.
elim;rewrite /=;intros.
- rifliad. by rewrite !inE (eqP H) eqxx /=. by rewrite !inE eq_sym H. by rewrite !inE. 
- rifliad. rewrite /= !inE (eqP H0) eqxx /=. lia. rewrite /= !inE. rewrite neg_sym. rewrite (negbT H0) /= H. done.
  rewrite !inE H. by rewrite orbA.  
- rewrite !big_map. rewrite !inE. kb (p == ptcp_from a). kb (p == ptcp_to a). 
  clear Heqn Heqn0. induction l. rewrite !big_nil !inE. lia. 
  rewrite !big_cons !inE H //=. rewrite IHl. rewrite orbA. kb (p \in ptcps_of_g a0).  kb (i \in fv a0). kb (p \in ptcps_of_g g1). lia. 
  by rewrite andbC /= orbC /=.  intros. apply H. auto. 
Qed. *)


(*Lemma big_ptcp_subst : forall l p g1 i, (p \in \bigcup_(j <- l) ptcps (j)[s g1 // i]) = (p \in \bigcup_(j <- l)  ptcps j) || ((i \in \bigcup_(j <- l) fv j) && (p \in ptcps g1)).
Proof.
elim;intros;rewrite /= ?big_nil ?big_cons !inE. lia. rewrite H !ptcp_subst orbA. kb (p \in ptcps a). kb (i \in fv a).  
kb (p \in ptcps g1). lia. kb ((p \in \bigcup_(j <- l) j)). kb ( (p \in \bigcup_(j <- l) g1)). rewrite andbC /=. done. lia. 
Qed.*)

(*Lemma big_ptcp_subst_if : forall l g1 i, (\bigcup_(j <- l) ptcps (j)[s g1 // i]) = 
                                                      if i \in \bigcup_(j <- l) fv j
                                                          then \bigcup_(j <- l)  ptcps j `|` (ptcps g1) 
                                                          else \bigcup_(j <- l) ptcps j.
Proof.
elim;intros;rewrite /= ?big_nil ?big_cons !inE. done. rewrite H !ptcps_subst. case_if; rewrite H0 /=.  rifliad. fsetPtac. 
fsetPtac. case_if. fsetPtac. fsetPtac.
Qed.
*)
(*Lemma same_vars_subst : forall e0 e1 n, same_vars e0 -> same_vars e1  -> same_vars e0[s e1//n].
Proof. elim;rewrite /=;rs;intros.  rifliad. done. rifliad. simpl. rs. auto. auto.
split_and. rewrite all_map. apply/allP=>g' Hin. simpl. erewrite nth_map. rewrite !fv_subst. apply/eqP. f_equal. 
by apply/eqP/(allP H2). Admitted.*)
(*Lemma ueqe_subst : forall e0 e1 e' n, same_vars e0 -> same_vars e1 -> bound e' ->  e0 =f= e1 ->  e0[s e'//n] =f= e1[s e'//n].
Proof. 
pcofix CIH.  intros. punfold H3. ich H3;simpl;auto.  ich H.
pfold. constructor. right.  apply : CIH. cc. cc. cc. done.
pfold. constructor. by rewrite !size_map.
have : (zip (map (fun e0' => (e0')[s e' // n]) gs)  (map (fun e0' => (e0')[s e' // n]) gs')) = map (fun p => (p.1[s e'//n ],p.2[s e'//n])) (zip gs gs'). clear H2 CIH H H0 H1 H4. elim : gs gs'.  destruct gs'. done. by simpl.  destruct gs'. done.
simpl.  f_equal. apply H. move=>->. move : H4. move/forallzipP=>HH. apply/Forall_forall. simpl in HH. intros. right. 
move : H3. move/nthP=>HH'. specialize HH' with (EEnd,EEnd). destruct HH'. rewrite -H4. erewrite nth_map. simpl.
erewrite nth_zip. simpl. move : H3.  rewrite size_map size_zip minnE H nat_fact. intros. simpl in H0. split_and.
apply : CIH. 
apply (allP H6). rewrite -H in H3.  cc. simpl in H1. split_and. apply (allP H7).  cc. done. 
(*rewrite -H in H1.  cc.
 cc. erewrite nth_zip.  simpl. move : H2.  rewrite size_map size_zip minnE H nat_fact. intros. cc. done.
rewrite nth_zip /=. *) suff : upaco2 Unravele bot2 (nth EEnd gs x0) (nth EEnd gs' x0). case. eauto. done. apply : HH. done. rewrite H. done. done.
move : H3. by rewrite size_map size_zip minnE H nat_fact. rs. 
rifliad. 
pfold. constructor. ich H. rewrite (eqP H3). right. 
rewrite -(@subst_nop _ (g[s ERec n g // n]) e' n). apply : CIH. cc. Admitted. *)
(*rewrite -(eqP H1). done. 
rewrite in_subst negb_and. apply/orP. right. by rewrite /= !inE. 
ich H. pfold. constructor.  right.  have : ERec n0 g[e e' // n] = (ERec n0 g)[e e' //n].  rewrite /= H1. done. move=>->. rewrite subst_distr. 
apply : CIH. cc. rewrite -H2.  done. cc. lia. simpl. apply/fsubsetP=>k. rewrite !inE. split_and. done. rewrite !inE. done.
rifliad.*)



(*pfold. constructor. ich H. right. rewrite subst_diff. apply : CIH. cc. move : H0. unlock lpreds. rewrite /=. nth_lpreds 0 H1. rewrite /bound. split_and.
rewrite Substitutions.efv_subst. simpl in H. done. rewrite /ebound. simpl. rewrite Substitutions.efv_subst.
simpl in H.  rewrite -(eqP H). apply/eqP/fsetP=>k. rewrite !inE. destruct (eqVneq k n0);rewrite /=. done.
destruct (eqVneq k n);rewrite /=. subst.
 Check (@subst_nop (g[e ERec n0 g // n]) e' n0). apply : CIH. rewrite -(eqP H2). cc. cc.  rewrite -(eqP H2). done.
 rewrite Substitutions.efv_subst. by rewrite /= !inE. cc. rewrite -(eqP H2). cc.

pfold. constructor. right. apply : CIH.
move : 
rewrite map_zip.
right. apply : CIH. move => e0 e1 e' n.*)



(*Add constraint that g1 participants is subset of g0's participants*)

Lemma fresh_for : forall S S', S' `<=` S -> fresh S \notin S'.
Proof.  intros. rewrite /fresh. destruct (atom_fresh_for_list S). apply/negP=>HH. apply : n. by apply (fsubset_in H). Qed.



(*Lemma project_pred_ptcps : forall a gs i p, lpreds (rec_pred) (GBranch a gs) -> p \in (fv (GBranch a gs)) -> i < size gs -> p \in  fv (nth GEnd gs i).
Proof. intros.  destruct (atom_fresh_for_list ([::ptcp_from a;ptcp_to a])). nth_lpreds 0 H=>HH. move : HH. 
rewrite /rec_pred.
rewrite !(@fv_project_eq _ x).  move : n. move/negP. rewrite !inE. rewrite /=. split_and. move : HH. rewrite (negbTE H1) (negbTE H3). 
Qed.

 Lemma project_pred_ptcps2 : forall a gs i p, lpreds rec_pred (GBranch a gs) -> i < size gs ->  (p \in  fv (nth GEnd gs i)) ->  (p \in fv (GBranch a gs)).
Proof. intros.  rewrite /= big_map.  rewrite foldr_exists. apply/hasP.  exists (nth GEnd gs i). cc. done. 
Qed.


Lemma project_pred_ptcps_set : forall a gs i, lpreds rec_pred (GBranch a gs) -> i < size gs -> fv (GBranch a gs) = fv (nth GEnd gs i).
Proof.
intros. apply/fsetP. move => x.  destruct ((x \in fv (nth GEnd gs i))) eqn:Heqn.
erewrite project_pred_ptcps2. done. cc. eauto. done. destruct ( (x \in fv (GBranch a gs)))eqn:Heqn2. erewrite project_pred_ptcps in Heqn. done. have : ipred x (GBranch a gs).  cc. intros.  cc. cc. cc. 
Qed.*)


(*Lemma full_unf : forall e n, econtractive (ERec n e) ->  full_eunf (ERec n e) = full_eunf (e[s ERec n e//n]).
Proof. intros. simpl in H.  split_and. rewrite /= -iterS iterSr /= emu_height_subst //=. Qed.

Lemma next_unf : forall e n, econtractive (ERec n e) -> next (ERec n e) = next (e[s ERec n e//n]).
Proof. intros. rewrite /next full_unf //=. Qed.

Lemma act_unf : forall e n, econtractive (ERec n e) -> act_of (ERec n e) = act_of (e[s ERec n e//n]).
Proof. intros. rewrite /act_of   full_unf //=. Qed.

*)

(*Lemma act_unf : forall e sigma, act_of e = act_of (e[e sigma]).
Proof.
elim;simpl;intros.   destruct n.  asimpl. simpl. done. simpl. done.
done. done. done. asimpl.
Lemma bisimilar_unf : forall e , bisimilar (ERec e) (e[ERec e.:ids]). 
Proof.
pcofix CIH. intros. pfold. constructor. simpl. 
elim;intros.
*)
(*
intros. pfold. punfold H0.  inversion H0. simpl in H.  split_and.  constructor;rewrite //=.
rewrite -H1 act_unf //=. split_and. 
rewrite -H2 next_unf //=. split_and. 
rewrite next_unf //=. split_and.*)
(*Qed.*)


Lemma f1eq : forall (n n0 : nat), [fset n] = [fset n0] -> n = n0.
Proof. 
intros. destruct (eqVneq n n0).   done. have : (n \in [fset n]) = (n \in [fset n0]). move : H.  move/fsetP=>Hff. rewrite -Hff //=.  rewrite !inE. rewrite (negbTE i) //=. Qed.


(*Lemma notin_subst : forall (a a2: endpoint) i, i \notin fv a -> a[s a2 // i] = a.
Proof.
elim;rewrite/=;rs;intros. move : H. rewrite !inE eq_sym. move/negbTE=>-> //=. done.
move : H0. rewrite !inE. move/orP=>[]. rewrite eq_sym. move=>-> //=. intros. rifliad.
rewrite H //=. f_equal. rewrite H //=. f_equal.  move : H0. rewrite big_map. induction l. rewrite !big_nil //=. 
rewrite !big_cons.rewrite !inE.  split_and. simpl. f_equal. apply H. done. done. apply IHl. auto. done. 
Qed.*)

(*Lemma double_subst : forall (e0 : endpoint) e1 e2 i, i \notin fv e1  -> e0[s e1 // i][s e2 // i] = e0[s e1 // i].
Proof.
intros. rewrite subst_nop. done. rewrite /bound in H.  rewrite fv_subst //=. rewrite !inE //=. by apply/eqP. 
Qed. 

Lemma eunf_subst : forall e0 e1 k, bound e1 ->  eunf e0[s e1 // k] = (eunf e0)[s eunf e1 // k].
Proof.
elim;rewrite /=;rs;intros.
-  rifliad. 
- done. 
- rifliad. rs. rewrite (eqP H1) double_subst.  done. rewrite [_[s eunf e1 // _]]subst_nop. done. rewrite fv_subst.  rewrite !inE //=.
rs. rewrite /bound in H0. rewrite (eqP H0).

Lemma bisim_unf_act : forall e0 e1 e' i, act_of e0 = act_of e1 -> act_of e0[s e'// i] = act_of e1[s e'//i].
Proof.
intros. move : H.  rewrite /act_of. Print full_eunf.
elim;rewrite /=;intros;rs.  move : H. rewrite {1}/act_of /=. destruct e1. rewrite {1} /act_of /=. case. 
intros. subst. rewrite /act_of /=. rs. done. done. all : try done. rewrite /act_of /=. rs. 
rewrite -iterS iterSr /=. /=. intros .destruct (full_eunf e1);try done;intros. rifliad. rifliad.
intros. rewrite /act_of.
remember (emu_height e0). remember (emu_height e1). move : n e0 e1 Heqn Heqn0 H. elim.
move => e0 e1. remember (emu_height e1). move : n Heqn. elim. simpl. 
intros. destruct e0,e1;rs;rewrite /=. move : H. rs. Search _ (_ = [fset _]). move => Hn0.
destruct (n == n0) eqn:Heqn2. 
- rifliad. move : H1. rewrite -(eqP H). rewrite eq_sym Heqn2 //=. 
  move : H.  rewrite -(eqP H1) Heqn2 //=. simpl. apply f1eq in Hn0. subst. rewrite eqxx //= in Heqn2. 
 * rs_in H. by apply fset_nil in H.  done. done. all : try done. rs_in H. symmetry in H. by apply fset_nil in H. 
  intros.    simpl in H1. simpl in H. simpl. 
Search _ ([fset _]).
simpl. 2 : { have : (n \in [fset n]) = (n \in [fset n0]). move : Hn0.  move/fsetP=>Hff. rewrite -Hff. done. 
        rewrite !inE Heqn2. done.}
[fset _]). intros. (move => e0 e1 H H1. 
remember (emu_height e1). 
rewrite /=.
intros.
elim;intros. destruct e1;rewrite /=;rs;try done
intros. rifliad. rewrite -(eqP H1) in H2. rs_in H. have :( n \in [fset n]) = (n \in [fset n0]).  move : H. move/fsetP.
move=>HH.  rewrite -HH. rewrite !inE. done. rewrite !inE eq_sym H2 //=. 
intros. exfalso. inversion H.  move : H. 
Lemma bisim_unf : forall e0 e1 e' i, econtractive e0 -> econtractive e1 -> fv e0 = fv e1 -> bisimilar e0 e1 -> bisimilar e0[s e'// i] e1[s e'//i].
Proof.  
intros. rewrite econtractive_subst. punfold H0. inversion H0. subst. pfold. constructor.

rewrite act_
intros.*) 

(*Check next.
Print next.

Lemma bound_branch : forall a gs g, bound (GBranch a gs) -> g \in gs -> bound g.
Proof.
intros. move : H. rewrite /bound /=. rs. rewrite big_map. intros. apply/eqP/fsetP=>k. apply/bool_iff.
split. rewrite -(eqP H). intros. rewrite big_exists. apply/hasP. exists g. done. done.
rewrite !inE. done.
Qed.

Print project_pred.

Fixpoint project_pred2 (S : fset_ptcp)  (g : gType) :=
  match g with
  | GRec _ g0 => project_pred2 S g0
  | GMsg _ _ g0 => project_pred2 S g0
  | GBranch a gs =>
      (all
        (fun g' : gType => all (fun p : ptcp => bisimilar (project (nth GEnd gs 0) p) (project g' p)) S)
        gs) && (all (project_pred2 S) gs)
  | _ => true
  end.*)

(*Lemma traverse_project_pred_unf : forall g0 g1 i, lpreds (svpred::rec_pred) g0 -> project_pred2 (ptcps g1) g0 -> lpreds (bound::ppred::nil) g1 -> ppred g0[s g1// i].
Proof. 
intros. destruct (i \notin fv g0) eqn:Heqn. rewrite subst_nop //=. split_and. cc.
elim : g0 g1 i Heqn H H0 H1;intros;rewrite /=. 
- move : Heqn. rewrite /= !inE. move/negbT. rewrite !inE. rewrite eq_sym.  rs. move=>->. cc. done. 
- move : Heqn. rs.  rewrite /= !inE. move/orP/orP. rewrite !inE. split_and. have: n == i = false by lia. move=>->. 
  simpl. apply H. by rewrite H4. cc. 
  split_and. cc.   (*nth_lpreds 0 H0. rewrite /bound. rs. move/eqP/fsetP.  move => HH. have : i \in fset0.  rewrite -HH !inE H3 H4 //=. 
  rewrite !inE //=. done. cc. *)rs. simpl in H1. apply H. cc. cc. simpl in H1. done. cc.
- rewrite /= !big_map !all_map big_ptcp_subst_if. split_and. rifliad. clear Heqn.
 * apply/allP=> x' Hin. simpl. apply/allP=>p. rewrite !inE. intros. 
   nth_lpreds 3 H0. simpl. split_and. destruct (orP H4). 
  ** rewrite (eqP H7). rewrite (@nth_map _ GEnd). rewrite !project_subst. erewrite project_tw0.
     erewrite (@project_tw0 x').
     rewrite !subst_nop. apply (allP (allP H5 _ Hin)). rewrite !inE. apply/orP. left. apply/eqP. reflexivity.
     rewrite -fv_eq. 
(*have : bound x'. apply : bound_branch. cc. done. rewrite /bound. move/eqP=>->. rewrite !inE //=. 
     cc. *)
rewrite -fv_eq. have : bound (nth GEnd l 0). apply : bound_branch. cc. cc. rewrite /bound. move/eqP=>->. rewrite !inE //=.
     cc. cc. rewrite /npred. apply/fresh_for. apply/fsubsetP=>x. intros. rewrite !inE. apply/orP. right.
     apply/orP. left. rewrite big_exists. apply/hasP. exists x'. done. done.
     rewrite /npred. apply/fresh_for. apply/fsubsetP=>x. intros. rewrite !inE. apply/orP. right.
     rewrite big_map big_exists. apply/hasP. exists x'. done. done.

     cc.
     rewrite /npred. apply/fresh_for. apply/fsubsetP=>x. intros. rewrite !inE. apply/orP. right.
     apply/orP. left. rewrite big_exists. apply/hasP. exists (nth GEnd l 0). cc. done. 
     rewrite /npred. apply/fresh_for. apply/fsubsetP=>x. intros. rewrite !inE. apply/orP. right.
     rewrite big_map. rewrite big_exists. apply/hasP. exists (nth GEnd l 0). cc. done. 
     cc. cc. cc.
  ** clear H4. 
  ** split_and. destruct (orP H8). by rewrite (negbTE H7) (negbTE H9) /= in H4. 
     destruct (orP H4). rewrite (@nth_map _ GEnd). rewrite !project_subst. 
     rewrite !subst_nop.  apply (allP (allP H5 _ Hin)). 
     rewrite !inE. apply/orP. right. split_and. eauto. eauto. 
     apply/orP. right. rewrite big_map. done. 

     rewrite -fv_eq.

     have : bound x'. apply : bound_branch. cc. done. rewrite /bound. move/eqP=>->. rewrite !inE //=. 
     cc. rewrite -fv_eq. have : bound (nth GEnd l 0). apply : bound_branch. cc. cc. rewrite /bound. move/eqP=>->. rewrite !inE //=.
     cc. cc. cc. cc. 
     
     rewrite (@nth_map _ GEnd). rewrite !project_subst. 
     rewrite !subst_nop. simpl in H1. split_and. apply (allP (allP H11 _ Hin)). eauto. 

     rewrite -fv_eq.

     have : bound x'. apply : bound_branch. cc. done. rewrite /bound. move/eqP=>->. rewrite !inE //=. 
     cc. rewrite -fv_eq. have : bound (nth GEnd l 0). apply : bound_branch. cc. cc. rewrite /bound. move/eqP=>->. rewrite !inE //=.
     cc. cc. cc. cc.
- rs_in Heqn. by rewrite big_map H3 in Heqn.
- apply/allP=>x.  intros. simpl. rs. apply H. done. apply/negP/negP. nth_lpreds 1 H0. simpl. move => HH.  
  split_and. move : Heqn. move/negP/negP. rs. rewrite big_map big_exists. move/hasP=>[]. intros.
  rewrite -(eqP (allP H4 _ H3)). move : p. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H7 in q. 
  have : nth GEnd l x1 \in l. cc. move=> Hin. 
  rewrite -(eqP (allP H4 _ Hin)) in q. done. 
  cc. simpl in H1. split_and. apply (allP H5 _ H3). cc.
Qed.*)





Lemma ch_diff : forall g a0 aa a1, linear g -> Tr (a0::(aa++[::a1])) g  -> Forall ( fun a => (ptcp_to a) \notin a1) (a0::aa) ->  Forall (fun a => action_ch a != action_ch a1) (a0::aa).
Proof.
intros. apply/List.Forall_forall. intros. 
destruct (eqVneq (action_ch x) (action_ch a1)); last done. inversion H1. subst.
exfalso. simpl in H2. destruct H2. 
- subst. apply : no_indep. apply : H5.  apply H6. move : H.  move/linearP/Linear_1=>HH.  apply : HH. 
  rewrite -[_::_]cat0s in H0. apply : H0. rewrite /same_ch. apply/eqP. done.
- apply List.in_split in H2.  destruct H2,H2. rewrite H2 in H0. move : H. move/linearP=>HH.  rewrite /Linear in HH.
  specialize HH with (a0::x0) x x1 a1. 
have : (a0 :: (x0 ++ (x :: x1)%SEQ)%list ++ [:: a1]) = ((a0 :: x0) ++ x :: x1 ++ [:: a1]).
  rewrite /=. f_equal. rewrite -catA. f_equal.


  intros. move : H0.  rewrite x2. move/HH=>H3. 
  have : same_ch x a1. by rewrite /same_ch e. move/H3. case. intros. move : H1.  
  rewrite H2. intros. inversion H1. apply List.Forall_app in H7. destruct H7. inversion H8. apply : no_indep. 
  apply H11.  apply H12.  done.
Qed.
Open Scope subst_scope.

Lemma size_pred_subst_ren : forall g sigma, size_pred g -> size_pred (g ⟨g sigma⟩).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto. split_and. rewrite size_map //=.
rewrite all_map. apply/allP=>g HH.  simpl. apply H. done. apply (allP H2). done.
Qed.

Lemma size_pred_subst : forall g sigma, (forall x, size_pred (sigma x)) -> size_pred g -> size_pred (g[g sigma]).
Proof.  
elim;intros;rewrite /=;simpl in *;try done;auto.
- rifliad. rifliad. simpl. asimpl.   apply H. intros. destruct x. asimpl. done. asimpl. 
apply/size_pred_subst_ren. auto. done.
- rewrite all_map. split_and. rewrite size_map. split_and. apply/allP=> ll Hin /=. apply H. done. split_and. apply (allP H3). done. 
Qed.


(*Lemma spred_bisim : forall g0 g1, contractive2 g0 -> contractive2 g1 -> bisimilarg g0 g1 -> spred g0 -> spred g1.
Proof.
elim;intros.
- punfold H1. inversion H1. subst. destruct g1;try done. simpl. simpl in *. split_and. rewrite nextg_unf  //=in H4.
B*)
Print step.
Lemma step_tr : forall g vn g', step g vn g' ->  exists s, Tr (s ++ [::vn.1]) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) s.
Proof.
move => g vn g'. elim.
- intros. exists nil. rewrite /=. auto.
- intros. exists nil. rewrite /=. split;auto.  apply TRBranch with (n:=n)(d:=GEnd). done. done.
- intros.  destruct H1,H1.  exists (a::x). rewrite /=. auto. 
- intros. move : H2.  move/forallzipP=>/=Hall. specialize Hall with GEnd 0.
  have : exists s0 : seq action,
           Tr (s0 ++ [:: l.1]) (nth GEnd gs 0) /\ Forall (fun a : action => ptcp_to a \notin l.1) s0. apply Hall;eauto.
  cc. move => []. intros. exists (a::x). destruct p.  split;auto. simpl. econstructor. 2 : { eauto. }  cc.
- intros. destruct H3,H3.  exists x. split;auto. apply/bisim_Tr;eauto. cc. cc. apply/bisim_sym. done.
Qed.


Lemma distinct_ch : forall g vn g', step g vn g' -> exists s, Tr (s ++ [::vn.1]) g /\  Forall (fun a =>  (action_ch a) != (action_ch vn.1)) s.
Proof. intros. edestruct (step_tr). eauto. destruct H0. exists x. split;auto. inversion H1. done. apply : ch_diff. Check ch_diff.  cc. 
subst. eauto.  auto. 
Qed.

Lemma distinct_ch_msg : forall a u g vn g', step (GMsg a u g) vn g' -> ptcp_to a \notin vn.1 -> (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto.   destruct H1. move : H2. move/Forall_forall=>HH.  destruct x. simpl in H1. inversion H1. subst. rewrite !inE in H0. split_and. simpl in H1.  inversion H1. subst. apply HH. rewrite !inE. done.
Qed.

Lemma distinct_ch_branch : forall a gs vn g', step (GBranch a gs) vn g' -> ptcp_to a \notin vn.1 ->  (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto. destruct H1. move : H2. move/Forall_forall=>HH.  destruct x. simpl in H1. inversion H1. subst. rewrite !inE in H0. split_and. simpl in H1.  inversion H1. subst. apply HH. rewrite !inE. done.
Qed.

(*Fixpoint clean e := 
match e with 
| EMsg d c v e0 => EMsg d c v (clean e0)
| EBranch d c es => EBranch d c (map clean es)
| ERec e0  => if clean e0 == EVar 0 then EEnd else if 0 \in endpoint_fv e0 then ERec (clean e0) else clean e0
| EVar j => EVar j
| EEnd => EEnd
end.*)

Print up_gType_gType.

Print gType_fv. 
Open Scope nat_scope.
Print gType_fv.
Fixpoint efvg (g : endpoint) : {fset (nat * bool)} := 
match g with 
| EMsg _ _ u g0 => [fset (n,true) | n in endpoint_fv g  (* (fvg g0) *)]
| EBranch _ _ gs  => [fset (n,true) | n in endpoint_fv g (*(\bigcup_(i <- (map fvg gs )) i)*) ] 
| ERec g0  => [fset ((n.1).-1,n.2) | n in (efvg g0) & n.1 != 0]
| EVar n => [fset (n,false)]
| EEnd => fset0
end.

Lemma eguarded_fvg1 : forall g i, eguarded i g -> (i,false) \notin efvg g.  
Proof.
elim;rewrite /=;try done;intros;rewrite ?inE //=.
lia. apply/imfsetP=>[]/= [] x /=. rewrite !inE. split_and. inversion q. 
subst. apply/negP. apply : H. eauto. have : x.1.-1.+1 = x.1 by lia. move=>->.
destruct x.  simpl in *. subst. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
apply/imfsetP=>[] [] /= x HH []. done. 
Qed.

Lemma eguarded_fvg2 : forall g i, ((i,false)  \notin efvg g) -> eguarded i g.
Proof.
elim;rewrite /=;try done;intros.
move : H. rewrite !inE. simpl. lia.
apply H. move : H0.  move/imfsetP=>HH. apply/negP=>HH'. apply/HH. rewrite /=. 
exists (i.+1,false). rewrite !inE. split_and. 
rewrite /=. done. 
Qed.

Lemma guarded_fvg : forall g i, eguarded i g <-> ((i,false) \notin efvg g).  
Proof.
intros. split;intros; auto using eguarded_fvg1, eguarded_fvg2. 
Qed.

Definition injective_for (S : {fset nat}) (f : nat -> nat) := forall n0 n1, n0 \in S -> n1 \in S -> f n0 = f n1 -> n0 = n1. 


Lemma cont_project : forall g p, econtractive2 (project g p).
Proof.
elim;rewrite //=;intros. 
- case_if.  
  * simpl. split_and. done. 
  
- rifliad; try done. 
  simpl. 
  done. 
  simpl. 
  done. 
- rifliad.  
  simpl. rewrite all_map.  
  apply/allP. 
  intro. intros. 
  simpl. 
  apply H. 
  done.


  simpl. rewrite all_map.  
  apply/allP. 
  intro. intros. 
  simpl. 
  apply H. 
  done.

destruct l.  
done. 

apply H. 
rewrite inE eqxx. done. 
Qed. 




Lemma fv_lt : forall g p n, n \in (endpoint_fv (project g p)) -> n \in (gType_fv g).
Proof. 
elim. 
intros. 
move : H. 
rewrite /= inE. 
done.

intros. 
move : H. 
rewrite /= inE. 
done.

intros. 
move : H0. 
rewrite /= ?inE. 
case_if; intros.  
apply/imfsetP. 
simpl in *. 
move : H1. move/imfsetP. 
move=>[]. 
simpl. 
intros. 
exists n.+1.
rewrite !inE /=. 
split_and. 
subst. 
rewrite !inE /= in p0. 
split_and. 
destruct x. 
done. 
simpl. 
apply : H. 
apply : H1. 
lia. 
rewrite /= inE //= in H1. 

intros. 
move : H0. 
rewrite /=. 
rifliad. 
rewrite /= ?inE. 
move/H. 
eauto. 

rewrite /= ?inE. 
move/H.  
done. 
move/H. 
done. 

intros. 

move : H0. 
rewrite /=. 
rifliad; simpl.  
all : rewrite !big_map. 
all : rewrite !big_exists. 
move/hasP=>[]. intros.  
apply/hasP.
exists x.  
done. 
apply : H. 
done. 
apply : q. 
move/hasP=> []. intros.  
apply/hasP. 
exists x. 
done. 
apply : H. 
done. 
apply : q. 
destruct l. 
rewrite inE. 
done. 
intros. 

simpl.
apply/orP. 
left. 
apply/H. 
auto. 
apply : H2. 
Qed. 

Lemma bound_proj : forall g p i, bound_i i g -> ebound_i i (project g p). 
Proof.
elim;intros.   
rewrite /=.
rewrite /= in H. 
done.
done.
rewrite /=.
rewrite /= in H0. 
case_if. 
rewrite /=.
apply H. 
done.
done.
simpl in *.
rifliad; rewrite //=.
apply H. 
done.
apply H.
done.
apply H.
done.
simpl in *. 
rifliad; rewrite /=.  
rewrite /= all_map. 
apply/allP. intro. 
intros. 
rewrite /=.
apply H. 
done.
apply (allP H0). 
done.
rewrite /= all_map. 
apply/allP. 
intro. 
intros.
rewrite /=.
apply H.
done.
apply (allP H0). 
done.
destruct l. 
done.
apply H. 
done.
simpl in *.
split_and. 
Qed. 

Lemma spred_proj : forall g p, spred g -> esize_pred (project g p). 
Proof.
elim;intros. 
rewrite /=. 
done.
done.
rewrite /=. 
case_if. 
rewrite /=. 
simpl in H0. 
auto. 
done. 
rewrite /=. 
rifliad. 
rewrite /=. 
apply H. 
rewrite /= in H0. 
done. 
rewrite /=. 
apply H. 
rewrite /= in H0. 
done.
apply H. 
done.
rewrite /=. 
rifliad. 
rewrite /=. 
split_and. 
rewrite /= size_map. 
rewrite /= in H0. 
split_and.
rewrite /= all_map. 
apply/allP. 
intro. 
intros. 
rewrite /=. 
apply H. 
apply H2. 
rewrite /= in H0. 
split_and.
apply : (allP H4). 
done.
rewrite /=.
split_and.
rewrite /= size_map. 
rewrite /= in H0. split_and. 
rewrite /= all_map. 
apply/allP. 
intro. 
intros.
rewrite /=. 
apply H. 
done. 
rewrite /= in H0. 
split_and.
apply (allP H5). 
done.
destruct l. 
done.
apply H. 
done.
rewrite /= in H0. 
split_and.
Qed. 








Lemma big_fset0 : forall gs g, g \in gs -> \bigcup_(j <- gs) gType_fv j = fset0 -> gType_fv g = fset0. 
Proof.
intros.
move : H0. move/fsetP=> HH. 
apply/fsetP=> k.  apply Bool.eq_true_iff_eq. 
split. 
rewrite /= -HH.  intros. rewrite /= big_exists. apply/hasP. 
exists g. done. done.  
rewrite /= inE. done.
Qed. 

Lemma bisim_proj : forall g0 g1 p, gpred g0 -> gpred g1 -> bisimilar g0 g1 -> ebisimilar (project g0 p) (project g1 p). 
Proof.
Admitted. 

Lemma step_test : forall g l g', step g l g' ->
Estep (project g (ptcp_from l.1)) (Sd,action_ch l.1,l.2) (project g' (ptcp_from l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. constructor.  
 rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * apply cont_project. 
  * apply bound_proj. done. 
  * apply spred_proj.  done.

- intros. rewrite /= ?eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_from a))).    apply estep_branch. 

  rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply cont_project. 
    rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/bound_proj. apply (allP H). done.
    rewrite /= size_map. done. rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/spred_proj. 
    apply (allP H8).  done. rewrite /= size_map. done. done.


- intros. move : H2. move/[dup]. intros. rewrite !inE in H2.  

rewrite /=. 
  split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H4).
  rifliad.
 * constructor. 
  * rewrite /epred. rewrite /gpred in H. unlock preds. unlock preds in H. simpl in *. split_and. 
    ** apply cont_project. 
    ** apply bound_proj. done. 
    ** apply spred_proj.  done.

    auto. apply H1.  apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg.  eauto. eauto. 

- intros. rewrite /=. move : H3. move/[dup]. move=>H3 Hdup.   rewrite !inE in H3. split_and. rewrite eq_sym. rifliad.
 * constructor.

  rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply cont_project. 
    rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/bound_proj. apply (allP H). done.
    rewrite /= size_map. done. rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/spred_proj. 
    apply (allP H13).  done. 





 auto. rewrite !size_map. done. apply/Forall_forall. move => x. 
   move/nthP=>HH. specialize HH with (EEnd,EEnd). destruct HH. 
 move : H6.  rewrite size_zip !size_map  H0 minnE nat_fact. intros. 
 rewrite nth_zip in H7. rewrite -H7 /=. 
   repeat erewrite (@nth_map _ GEnd _ EEnd (fun g => project g (ptcp_from l0.1))).  
   move : H2. move/Forall_forall=>Hall;intros. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') x0).
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H0.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. done. done. all: try done.  
   rewrite /= H0. done. 
   rewrite /= !size_map. done.

 * apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. eauto. eauto.  constructor.  

     rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply cont_project. 
    rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/bound_proj. apply (allP H). done.
    rewrite /= size_map. done. rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/spred_proj. 
    apply (allP H14).  done. 


auto. 
   by rewrite !size_map.
 * apply/(@forallP _ _ (EEnd,EEnd)).  intros. move : H2. move/Forall_forall=>HH0. specialize HH0 with (nth (GEnd,GEnd) (zip gs gs') x0).
   move : H7.   rewrite size_zip minnE !size_map H0 nat_fact=>H7. 

   rewrite nth_zip /= in HH0. rewrite nth_zip /=.  
   erewrite !nth_map. apply : HH0. rewrite -nth_zip. apply/mem_nth.  rewrite size_zip minnE H0 nat_fact. done.
   done. done. rewrite /= H0. done. by rewrite !size_map. done. apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. 
   eauto. eauto. 
 * rewrite !match_n.
   move : H2. move/Forall_forall=>Hall. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') 0). 
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H0.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. simpl in H4. 
   rewrite /gpred in H. unlock preds in H. simpl in *.  split_and. rewrite /= -H0. done. done. done.

- intros. econstructor.
  4 : {   eauto. }  

  rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * apply cont_project. 
  * apply bound_proj. done. 
  * apply spred_proj.  done.

 rewrite  /epred. rewrite /gpred in H0.  unlock preds. unlock preds in H0. simpl in *. split_and. 
  * apply cont_project. 
  * apply bound_proj. done. 
  * apply spred_proj.  done.

  apply bisim_proj. done. done. done.

Qed. 




Lemma step_test2 : forall g l g', step g l g' -> lpreds (bound::linear::rec_pred) g ->  Estep (project g (ptcp_to l.1)) (Rd,action_ch l.1,l.2) (project g' (ptcp_to l.1)).
Proof.  move => g l g'. elim.
- intros. rewrite /= eqxx.  rifliad. have : ptcp_from a != ptcp_to a.  cc. intros. by rewrite (eqP H0) eqxx in x. 
- intros. rewrite /= eqxx. rifliad. have : ptcp_from a != ptcp_to a.  cc. intros. by rewrite (eqP H1) eqxx in x. 
Check nth_map.
  erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_to a)));last done.    apply estep_branch. by   rewrite size_map.  

- intros. move : H1. move/[dup]. intros. rewrite !inE in H1.  rewrite /=. 
  split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H5).
  rifliad.
 * constructor. auto. apply H0.  cc. apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg.  eauto. eauto. cc. 
 * apply : H0. cc. 
- intros. Print Estep. rewrite /=. move : H2. move/[dup]. move=>H2 Hdup. rewrite !inE in H2. split_and.  rewrite [ptcp_to l0.1 == ptcp_to a]eq_sym. rewrite (negbTE H5) !match_n. rifliad.
 * Print Estep. constructor. auto. by rewrite !size_map.  apply/Forall_forall. move => x. 
   move/nthP=>HH. specialize HH with (EEnd,EEnd). destruct HH. 
 move : H6.  rewrite size_zip !size_map  H minnE nat_fact. intros. 
clear H4. rewrite nth_zip in H7. rewrite -H7 /=. 
   repeat erewrite (@nth_map _ GEnd _ EEnd (fun g => project g (ptcp_to l0.1))).  
   move : H1. move/Forall_forall=>Hall;intros. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') x0).
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. done. done. all: cc. 
   rewrite !size_map. done.
 * apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. eauto. eauto. cc.
   move : H1. move/forallzipP=>HH. simpl in HH. apply : HH. done. cc. cc.
- intros. (*have : lpreds rec_pred (GRec n g0) by cc. clear H3. move=> H3.*) rewrite /=. rifliad. 
 * rewrite !project_subst in H0.  rs_in H0. rewrite H2 (eqP H2) in H0.  rs_in H0. rewrite eqxx in H0. apply H0.  cc. 
 * apply traverse_project_pred_unf.  split_and. cc. cc. cc. econstructor.  apply : bisimilar_unf. apply bisimilar_refl. 

  rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0.   apply H0. cc. apply traverse_project_pred_unf. split_and. cc. cc. cc.
- rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0. rewrite !subst_nop in H0. apply H0. cc. 
 nth_lpreds 0 H1. rewrite /bound. move/eqP=><-. rs. apply/eqP. rewrite mem_fsetD1 //=. erewrite fv_eq. lia. cc. by apply/negbT. erewrite fv_eq. apply/negbT. eauto. cc. cc.
Grab Existential Variables. eauto.
Qed.


Lemma step_test3 : forall g l g', step g l g' -> lpreds (bound::linear::rec_pred) g ->  forall p, p \notin l.1 ->
 bisimilar (project g p) (project g' p).
Proof. 
move => g l g'. elim;intros.
- simpl in H0.  rewrite /=. move : H0. rewrite !inE. split_and.  rewrite (negbTE H1) (negbTE H2). 
- simpl in H1.  rewrite /=. move : H1. auto.  
- rewrite /=. intros. simpl in H1. move : H1. rewrite !inE. split_and. rewrite (negbTE H2) (negbTE H3) match_n.
  apply : project_predP_aux. cc. rewrite !inE. split_and. cc. 
- simpl.  rifliad. auto.  pfold. constructor. done. done. apply/forallzipP. by rewrite /=. intros. simpl. left.  
  simpl. rewrite /next.  simpl. auto. move : H5.  rewrite /=. destruct x0. simpl. intros. apply H0. cc. done. done. 
  pfold. constructor. done. done. apply/forallzipP. done.  intros. simpl. left. rewrite /next.  simpl. auto. move : H6. simpl.   destruct x0. simpl. intros. apply H0. cc. done. done. apply H0. cc. done.
 simpl. 

  rifliad. simpl. pfold. constructor. done. rewrite /next /= !size_map //=. apply/forallzipP. rewrite /next /= !size_map //=.
  intros. simpl. rewrite /next /=. left.   move : H6. rewrite /next /= size_map. intros. erewrite !nth_map. move : H1. move/forallzipP=>Hzip. simpl in Hzip. apply Hzip. all : try done. move : H6. intros. cc. by rewrite -H. 
  pfold. constructor. all : try done. by rewrite /next /= !size_map. apply/forallzipP. by rewrite /next /= !size_map.
  move => x0. rewrite /= /next /= size_map. intros. left.

simpl. rewrite /next /=. erewrite !nth_map. move : H1. move/forallzipP. move =>Hzip.  simpl in Hzip. apply Hzip.
  all : try done. cc. by rewrite -H. rewrite !match_n. move : H1. move/forallzipP=>Hzip. simpl in Hzip. apply : Hzip. all : try done. cc. cc. simpl. rifliad. specialize H0 with p. rewrite project_subst in H0. rewrite (eqP H3) /= H3 in H0. rs_in H0. rewrite eqxx in H0. apply H0. cc. apply traverse_project_pred_unf.  cc. cc. done. cc. apply bisimilar_unf. 
  specialize H0 with p. rewrite /= in H0. rewrite project_subst /= in H0. rewrite H3 H4 in H0. apply H0. cc. apply traverse_project_pred_unf.  cc. simpl. cc. done. cc. 
  
  specialize H0 with p.  rewrite /= project_subst /= in H0.  rewrite H3  H4  in H0. 
  rewrite (@subst_nop endpoint_substType) in H0. apply H0. cc. apply traverse_project_pred_unf. cc. simpl.  cc. done.
  rewrite H4 //=.  cc.
Grab Existential Variables. all : repeat constructor.
Qed.

(*Operational correspondance, completeness direction*)
Lemma harmony1 : forall g l g' S, lpreds (bound::linear::rec_pred) g -> step g l g' -> l.1 `<=` S -> 
 EnvStep (projmap S g) l (projmap S g').
Proof.
intros.
have :  projmap S g =  (projmap S g).[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g (ptcp_from l.1)].[ptcp_to l.1 <- project g (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H3). 
by rewrite (eqP H4). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H3. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H4 HH. by rewrite mapf_if H2.
exfalso. apply/negP. apply (negbT H2). apply : (fsubset_in). eauto. rewrite !inE H3. lia. exfalso. apply/negP. apply (negbT H2). apply : (fsubset_in). eauto. rewrite !inE H3. lia. rewrite fnd_rem1 H3 fnd_rem1 H4. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H2. done. 
move=>->.

have :  projmap S g' =  (projmap S g').[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g' (ptcp_from l.1)].[ptcp_to l.1 <- project g' (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H3). 
by rewrite (eqP H4). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H3. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H4 HH. by rewrite mapf_if H2.
exfalso. apply/negP. apply (negbT H2). apply : (fsubset_in). eauto. rewrite !inE H3. lia. exfalso. apply/negP. apply (negbT H2). apply : (fsubset_in). eauto. rewrite !inE H3. lia. rewrite fnd_rem1 H3 fnd_rem1 H4. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H2. done. 
move=>->.
constructor. 
apply step_test. done. cc.
apply step_test2. done. cc.
by rewrite /projmap /=.
move => p e e'. rewrite !fnd_rem1. rifliad. rewrite /projmap !mapf_if. rifliad. move=>[] HH [] HH0. subst. apply : step_test3. eauto. cc. by rewrite !inE H2 H3. case. move=>->. auto. move=>[] ->. auto. move=>[]->. auto. 
Qed.
