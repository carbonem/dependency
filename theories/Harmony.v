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
| estep_msg d c v e0  : Estep (EMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d vn c c' v e0 e0'  : Estep e0 (d,c,vn) e0' -> c <> c' -> 
                                        Estep (EMsg Sd c' v e0) (d,c,vn) (EMsg Sd c' v e0')
| estep_branch n es d c   :   n < size es -> Estep (EBranch d c es) (d,c, inr n) (nth EEnd es n)
| estep_branch_async es0 es1 vn d c c'  : size es0 = size es1 -> Forall (fun p =>  Estep p.1 (d,c,vn) p.2) (zip es0 es1) -> c <> c' -> Estep (EBranch Sd c' es0) (d,c,vn) (EBranch Sd c' es1)
| estep_rec e l e' : epred (ERec e) -> Estep e[e (ERec e).:ids] l e' -> Estep (ERec e) l e'.
(*| estep_rec e l e1 e' : epred e -> epred e1 ->  ebisimilar e e1 -> Estep e1 l e' -> Estep e l e'.*)
Set Elimination Schemes.
Hint Constructors Estep.


Lemma Estep_ind
     : forall P : endpoint -> dir * ch * (value + nat) -> endpoint -> Prop,
       (forall (d : dir) (c : ch) (v : value) (e0 : endpoint), P (EMsg d c v e0) (d, c, inl v) e0) ->
       (forall (d : dir) (vn : value + nat) (c c' : ch) (v : value) (e0 e0' : endpoint), 
        Estep e0 (d, c, vn) e0' -> P e0 (d, c, vn) e0' -> c <> c' -> P (EMsg Sd c' v e0) (d, c, vn) (EMsg Sd c' v e0')) ->
       (forall (n : nat) (es : seq endpoint) (d : dir) (c : ch),  n < size es -> P (EBranch d c es) (d, c, inr n) (nth EEnd es n)) ->
       (forall (es0 es1 : seq endpoint) (vn : value + nat ) (d : dir) (c c' : ch),
        size es0 = size es1 ->
        Forall (fun p : endpoint * endpoint => Estep p.1 (d, c, vn) p.2) (zip es0 es1) ->
        Forall (fun p : endpoint * endpoint => P p.1 (d, c, vn) p.2) (zip es0 es1) ->
        c <> c' -> P (EBranch Sd c' es0) (d, c, vn) (EBranch Sd c' es1)) ->
  (*     (forall (e : endpoint) (l : dir * ch * (value + nat) ) (e1 e' : endpoint), epred  e -> epred e1 ->
        ebisimilar e e1 -> P e1 l e' -> P e l e') ->*)
     (forall (e : endpoint) (l : dir * ch * (value + nat) ) ( e' : endpoint), 
         P e[e (ERec e).:ids] l e' -> P (ERec e) l e') ->
       forall (e : endpoint) (p : dir * ch * (value + nat)) (e0 : endpoint), Estep e p e0 -> P e p e0.
Proof.
intros. move : e p e0 H4. fix IH 4;intros. destruct H4.
- apply H;auto.
- apply H0;auto.
- apply H1;auto.
- apply H2;auto. elim : H5;auto. 
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
                           domf Δ = domf Δ' -> (forall p e e',  Δ.[? p] = Some e -> Δ'.[? p] = Some e' -> unfeq e e') -> EnvStep Δ.[ptcp_from l.1 <- e0].[ptcp_to l.1 <- e1] l  Δ'.[ptcp_from l.1 <- e0'].[ptcp_to l.1 <- e1'].
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
(*Lemma fv_eq1 : forall g p n, lpreds rec_pred g  -> n \in endpoint_fv (project g p) -> n \in gType_fv g. 
Proof. Admitted.*)
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
     cc. cc. rewrite /npred. apply/rewrite fresh_for. apply/fsubsetP=>x. intros. rewrite !inE. apply/orP. right.
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
- intros. destruct H1,H1. exists x. split;auto. 
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



Inductive NG : gType -> Prop :=
| NG_end : NG GEnd
| NG_var n : NG (GVar n)
| NG_next g : NG g -> NG (GRec g).
Hint Constructors NG.

Lemma NGP : forall g n, ~ guarded n g -> NG g.
Proof.
elim;intros;auto. 
simpl in *. constructor.   apply: H. eauto. done. done.
Qed. 


Definition no_step g := forall l g', ~ step g l g'.

Definition no_estep g := forall l g', ~ Estep g l g'.

Inductive no_step_f  (r : gType -> Prop) : gType -> Prop :=
 | no_step_c g : no_step g -> no_step_f r g
 | no_step2 g: r (g [g (GRec g).:ids]) -> no_step_f r (GRec g).


Notation NoStep := (paco1 no_step_f bot1).  Check paco2. 

Lemma no_step_lt : forall g (r1 r2 : gType -> Prop ), (forall g, r1 g -> r2 g) -> no_step_f r1 g -> no_step_f r2 g.
Proof.
intros. inversion H0. subst. constructor. done.  
subst. apply no_step2.  apply H.  done.
Qed. 


Inductive MUE : endpoint -> Prop :=
| MU_end : MUE EEnd
| MU_mu e : MUE (e [e (ERec e) .: ids])  -> MUE (ERec e).
Hint Constructors MUE. 
Lemma MUE1 : forall e i sigma, ~ eguarded i e -> sigma i = EEnd -> MUE (e [e sigma]).
Proof.
elim;intros; simpl in *. have : n = i. lia. move=>->. rewrite /= H0. done. done.
asimpl. constructor. 

have : 
 [eERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: sigma] e =

([e(ERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e))..] ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e)).
asimpl.  done. intros. rewrite /= -x. 
simpl in *.
apply : H.  eauto.  simpl in *. done.
done.
done.
Qed.



(*Lemma MUE_cont : forall e, MUE e -> econtractive2 e.apply
Proof.
move => e. elim.  done. intros.  simpl in *. *)

Lemma MUE_no_step : forall e, MUE e -> no_estep e. 
move => e. elim. intro. intros. intro. inversion H. 
intros.  intro. intros. intro. inversion H1.  subst. apply : H0. eauto. 
Qed.


Lemma inject_notin : forall e sigma v, injective sigma ->  v \notin endpoint_fv e -> sigma v \notin endpoint_fv (e ⟨e sigma ⟩). 
Proof.
intros.   suff : sigma v \in endpoint_fv (⟨e sigma ⟩ e) -> v \in endpoint_fv e. 
intros. apply/negP.  intro. apply (negP H0). apply x. apply H1. clear H0. 
elim : e sigma v H;intros;simpl in *. rewrite /= inE in H0. rewrite /= inE.  apply/eqP. apply H. lia. 
rewrite /= inE in H0.  done.
move : H1.  move/imfsetP=> H'.  destruct H'. simpl in *. rewrite /= !inE in H1. split_and. 
apply/imfsetP. exists v.+1. simpl in *. rewrite /= inE.  split_and. destruct x.   done. simpl in *. subst. move : H3.  asimpl. intros. apply : H. instantiate (1 := (0 .: sigma >> succn)).  2 : {    simpl in *. done. } apply inject2. done. done. apply : H. 2 : { eauto. } done. 
move : H1. rewrite !big_map !big_exists. move/hasP=>HH. destruct HH. apply/hasP. exists x. done. apply : H. done. 2 : { eauto.  }  done. 
Qed.


(*Lemma inject_in : forall e sigma v, v \in endpoint_fv e -> (forall n, v \notin  endpoint_fv (sigma n)) -> v \notin endpoint_fv (e ⟨e sigma ⟩). 
Proof.
intros.   suff : sigma v \in endpoint_fv (⟨e sigma ⟩ e) -> v \in endpoint_fv e. 
intros. apply/negP.  intro. apply (negP H0). apply x. apply H1. clear H0. 
elim : e sigma v H;intros;simpl in *. rewrite /= inE in H0. rewrite /= inE.  apply/eqP. apply H. lia. 
rewrite /= inE in H0.  done.
move : H1.  move/imfsetP=> H'.  destruct H'. simpl in *. rewrite /= !inE in H1. split_and. 
apply/imfsetP. exists v.+1. simpl in *. rewrite /= inE.  split_and. destruct x.   done. simpl in *. subst. move : H3.  asimpl. intros. apply : H. instantiate (1 := (0 .: sigma >> succn)).  2 : {    simpl in *. done. } apply inject2. done. done. apply : H. 2 : { eauto. } done. 
move : H1. rewrite !big_map !big_exists. move/hasP=>HH. destruct HH. apply/hasP. exists x. done. apply : H. done. 2 : { eauto.  }  done. 
Qed.*)


Lemma inotine2 : forall g i sigma, (forall n, i \notin  endpoint_fv (sigma n)) -> i \notin endpoint_fv g [e sigma].
Proof.
elim;rewrite /=;try done;intros. 
apply/imfsetP=>/=H'. destruct H'. rewrite !inE in H1.  destruct (andP H1). move : H3. asimpl. intros. apply/negP. apply : H. 2 : { apply : H3. } case. simpl. rewrite /= inE. lia. simpl. intros. asimpl. subst. specialize H0  with n.   apply (@inject_notin _ (succn)) in H0.  destruct x. done. simpl in *. apply H0. 
done.
rewrite !big_map !big_exists. apply/negP. move/hasP=>HH. destruct HH. apply/negP. apply : H. eauto. eauto. done. 
Qed.

Search "econtractive2_subst".


Lemma econtractive2_ren : forall g sigma, injective sigma -> (forall n, n <= sigma n) ->  econtractive2  g -> econtractive2 g ⟨e sigma ⟩.
Proof.
elim;intros;simpl;try done. 
asimpl. split_and. have : 0 = ( 0 .: sigma >> succn) 0. done. intros. rewrite {1}x.

rewrite -eguarded_shift. simpl in H2. split_and. auto.
apply H. auto.  case. done. done.  simpl in H2. split_and. apply H.  done. done. done.
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done.  done. done.  simpl in H2. apply (allP H2). done.
Qed.


Lemma econtractive2_subst : forall g sigma, econtractive2 g -> (forall n, econtractive2 (sigma n)) -> econtractive2 g [e sigma].
Proof. 
elim;rewrite /=;intros;try done. 
asimpl. split_and. 
apply/eguarded_sig2.
instantiate (1 := (EVar 0 .: (ids >>  ⟨e ↑ ⟩))).  asimpl. done.
case. done. simpl. intros. apply/eguarded_fv. asimpl. apply/inotine. done.
apply H. done.  intros. destruct n.  done. simpl. asimpl.  apply/econtractive2_ren. done. done. done.
apply H. done.  intros. done. 
rewrite all_map. apply/allP. intro. intros. simpl. apply H. done. apply (allP H0). done. done.
Qed.


Lemma cont_project : forall g p, econtractive2 (project g p).
Proof.
elim;rewrite //=;intros. 
- case_if.  
  * simpl. split_and. simpl. split_and. 
(*    apply eguarded_fv.  apply : inj_rem5. instantiate (1 := (1.:ids)).  instantiate (1 := (2.:ids)). 
    asimpl. apply inj_rem4'. 
    apply eguarded_fv2 in H0. rewrite /= H0. intros. rewrite /= inE in H1. rewrite /= (eqP H1). done. done. apply econtractive2_subst. done.
    case. done. simpl in *. intros. done.*)
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
simpl in *. rewrite /= inE in H1. done. 
(*move : H1. move/imfsetP=> HH. simpl in *. destruct HH. rewrite /= inE in H1. split_and. 
apply/imfsetP. exists n.+1. simpl in *. rewrite /= !inE.  split_and. subst. destruct x. done. simpl in *.  apply :H.  
apply : fv_aux.   Print scons. apply H3. simpl in *. done. eauto. 
Search _ gType_fv. 
simpl in *
rewrite /= inE //= in H1. *)

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

(*Lemma guarded_proj : forall g p i, guarded i g -> eguarded i (project g p).
Proof.
elim;intros; try done.
nnmmsimpl in *. case_if.  simpl in *. apply H. done.
done.
simpl in *. case_if. done. case_if. done. *)



(*Lemma no_step_lt2 : forall g (r1 r2 : gType -> Prop ), (forall g, r1 g -> r2 g) -> paco1 no_step_f r1 g -> paco1 no_step_f r2 g.
Proof.
pcofix CIH.  intros. pfold. punfold H1. inversion H1. subst. constructor. done.
subst.  apply no_step2. inversion H.  right. apply : CIH. eauto. done. right. apply : CIH. 
eauto. 

done. subst. *)

Lemma step_cont : forall g l g', step g l g' -> contractive2 g.
Proof.
move => g l g'. elim;intros.
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
simpl in *. unlock gpred in H. simpl in *. split_and. 
Qed. 

(*Lemma estep_cont : forall g l g', Estep g l g' -> econtractive2 g.
Proof.
move => g l g'. elim;intros.
simpl in *. unlock epred in H. simpl in *. split_and. 
simpl in *. unlock epred in H. simpl in *. split_and. 
simpl in *. unlock epred in H. simpl in *. split_and. 
simpl in *. unlock epred in H. simpl in *. split_and. 
simpl in *. unlock epred in H. simpl in *. split_and. 
Qed. *)




(*Lemma eguarded_NG : forall g i , ~ eguarded i g -> no_estep g. 
Proof.
elim;intros. 
simpl in *. intro.  intros. intro. inversion H0. done.
intro. intros. intro. apply : H. simpl in H0.  eauto. inversion H1. subst. 
simpl in *.

done.

Lemma NG_subst : forall g i (sigma : nat -> endpoint) , ~ eguarded i g -> (forall n, no_estep (sigma n)) ->  no_estep (g [e sigma ]). 
Proof.
elim;intros.  
simpl in *. done.
done.
simpl in *. asimpl.  rewrite /no_estep.  intros. intro. inversion H2. subst. 
have :  ([e(ERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e))..] ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e))  =
 [eERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: sigma] e. asimpl. done. intros. rewrite x in H5.
clear x.  

apply : H5. } case. simpl in *.



 apply Hinver






(forall n,  NoStep (sigma n)) ->  NoStep (g [g sigma]).
Proof.
pcofix CIH. intros.
inversion H0. 
simpl in *. pfold.  constructor. intro. intros. intro. inversion H2. simpl in *. specialize H1 with n.  
apply no_step_lt.
apply : H1. done.



zx
intros g sig H.  elim : H sig. 
intros. 
simpl in *. intro.  intros. intro.  inversion H0. 
intros.  simpl in *. done. 
intros. simpl in *. asimpl. 
rewrite /no_step.  intros. intro. inversion H2. subst. 

have : ([gGRec ([gvar 0 .: sig >> ⟨g ↑ ⟩] g0) .: var] ([gvar 0 .: sig >> ⟨g ↑ ⟩] g0)) =
[gGRec ([gvar 0 .: sig >> ⟨g ↑ ⟩] g0) .: sig] g0.
asimpl. done. intros. rewrite x in H5. 
clear x. apply : H0. 2 : { eapply H5. } intros.  destruct n.  simpl in *. 
rewrite /no_step. intros. intro. 

2 : { simpl in *. done. }

 case. simpl in *.

inversion H2.  subst.

 eapply  H5. 

apply H0. 
*)


Lemma step_test : forall g l g', step g l g' -> gpred g -> 
Estep (project g (ptcp_from l.1)) (Sd,action_ch l.1,l.2) (project g' (ptcp_from l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. constructor. (*  
 rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * apply cont_project. 
  * apply bound_proj. done. 
  * apply spred_proj.  done.*)

- intros. rewrite /= ?eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_from a))).    apply estep_branch.
  rewrite size_map.  done.  done. 
(*
  rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply cont_project. 
    rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/bound_proj. apply (allP H). done.
    rewrite /= size_map. done. rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/spred_proj. 
    apply (allP H8).  done. rewrite /= size_map. done. done.
*)

- intros. move : H2. move/[dup]. intros. rewrite !inE in H2.  

rewrite /=. 
  split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H5).
  rifliad.
 * constructor. 
  * apply H1.  move : H3. rewrite /gpred.  unlock preds. rewrite /=. split_and. 
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg.  eauto. eauto. 
  * apply H1.   move : H3. rewrite /gpred.  unlock preds. rewrite /=. split_and.
- intros. rewrite /=. move : H3. move/[dup]. move=>H3 Hdup.   rewrite !inE in H3. split_and. rewrite eq_sym. rifliad.
 * constructor.
  * rewrite !size_map.  done. 
  * apply/forallzipP. rewrite !size_map.  done. intros. simpl. rewrite size_map in H7.  repeat erewrite nth_map.  move : H2.  move/forallzipP. simpl. move => HH. 
    apply : HH. done.  done.  move : H4. rewrite /gpred.  unlock preds. rewrite /=. split_and. 
    apply (allP H2). apply/mem_nth. done. 
    apply (allP H4). apply/mem_nth. done. 
    apply (allP H15). apply/mem_nth. done. 
    apply (allP H14). apply/mem_nth. done. 
    apply (allP H13). apply/mem_nth. done. 
    rewrite -H0.  done.  done. 
    apply/eqP. rewrite neg_sym.  apply : distinct_ch_branch.  eauto. eauto. 
 * move : H7. move/eqP=> HH. rewrite HH eqxx in H5.  done. 
 * rewrite !match_n.  move : H2. move/forallzipP. simpl. move => HH. apply HH.   done. move : H. rewrite /gpred. unlock preds. simpl.  split_and. 
   move : H4. rewrite /gpred.  unlock preds. simpl. split_and.
      apply (allP H2). apply/mem_nth. done. 
    apply (allP H4). apply/mem_nth. done. 
    apply (allP H15). apply/mem_nth. done. 
    apply (allP H14). apply/mem_nth. done. 
    apply (allP H13). apply/mem_nth. done. 

- intros. simpl in *. case_if. constructor. 

 * rewrite /epred. unlock preds. rewrite /gpred in H. unlock preds in H. simpl in *. split_and. 
   apply cont_project. apply bound_proj. done. apply spred_proj. done.
   rewrite project_subst in H1. 
   simpl in *.

have : (project g0 (ptcp_from l0.1))[(GRec g0 .: var) >> project^~ (ptcp_from l0.1)] =
 ([e(ERec (project g0 (ptcp_from l0.1)))..] (project g0 (ptcp_from l0.1))).
asimpl. f_equal. fext. case. asimpl. rewrite /= H3.  done. intros. asimpl. simpl in *. done.
intros. rewrite /= -x. apply H1. 
  move : H2. rewrite /gpred. unlock preds. simpl. split_and. 
  apply contractive2_subst. done. case. simpl.  split_and. intros. simpl.  done. 
  
  apply bound_subst. 
 Search _ (bound_i _ (_ [g _])). 
done. intro. intros. destruct x1,x2;try done.  f_equal. simpl in *. inversion H1. done. 
rewrite project_subst in H1. move : H1. asimpl. rewrite /= H2. intros. 
have:  [eEEnd .: var >> project^~ (ptcp_from l0.1)] = [eEEnd .: ids]. fext. case;try done. intros.
rewrite x in H1. 
clear x.  apply estep_cont in H1 as HH. exfalso. apply : MUE_no_step. apply : MUE1. have: ~ eguarded 0 (project g0 (ptcp_from l0.1)).  lia. intros. apply : x. 2 : {  eapply H1. } simpl in *. done.

intro. intros. destruct x1,x2. done. simpl in *. done. simpl in *. done. f_equal. simpl in *. inversion H1.  done.
Qed.

Lemma step_test2 : forall g l g', step g l g' ->
Estep (project g (ptcp_to l.1)) (Rd,action_ch l.1,l.2) (project g' (ptcp_to l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. case_if. rewrite /gpred in H. unlock preds in H. simpl in *. split_and. rewrite neg_sym H0 in H5. done. 
  constructor.  
 rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * apply cont_project. 
  * apply bound_proj. done. 
  * apply spred_proj.  done.

- intros. rewrite /= ?eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_to a))).    

  case_if. rewrite /gpred in H. unlock preds in H. simpl in *. split_and. rewrite neg_sym H1 in H4. done.  
  apply estep_branch. 

  rewrite  /epred. rewrite /gpred in H.  unlock preds. unlock preds in H. simpl in *. split_and. 
  * rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply cont_project. 
    rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/bound_proj. apply (allP H). done.
    rewrite /= size_map. done. rewrite /= all_map. apply/allP. intro. intros. rewrite /=. apply/spred_proj. 
    apply (allP H9).  done. rewrite /= size_map. done. done.


- intros. move : H2. move/[dup]. intros. rewrite !inE in H2.  

rewrite /=. 
  split_and. rewrite neg_sym in H4. rewrite neg_sym in H5.   rewrite  (negbTE H5). 
  rifliad.
 * constructor. 
  * rewrite /epred. rewrite /gpred in H. unlock preds. unlock preds in H. simpl in *. split_and. 
    ** apply cont_project. 
    ** apply bound_proj. done. 
    ** apply spred_proj.  done.

    auto. apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg.  eauto. eauto. 

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
   repeat erewrite (@nth_map _ GEnd _ EEnd (fun g => project g (ptcp_to l0.1))).  
   move : H2. move/Forall_forall=>Hall;intros. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') x0).
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H0.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. done. done. all: try done.  
   rewrite /= H0. done. 
   rewrite /= !size_map. done.

 * apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. eauto. eauto.  
   rewrite neg_sym H6 in H5.    done. 

 * rewrite !match_n.
   move : H2. move/Forall_forall=>Hall. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') 0). 
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H0.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. simpl in H4. 
   rewrite /gpred in H. unlock preds in H. simpl in *.  split_and. rewrite /= -H0. done. done. done.

- intros. simpl in *. case_if. constructor. 

 * rewrite /epred. unlock preds. rewrite /gpred in H. unlock preds in H. simpl in *. split_and. 
   apply cont_project. apply bound_proj. done. apply spred_proj. done.



  rewrite project_subst in H1. 
simpl in *.


have : (project g0 (ptcp_to l0.1))[(GRec g0 .: var) >> project^~ (ptcp_to l0.1)] =
 ([e(ERec (project g0 (ptcp_to l0.1)))..] (project g0 (ptcp_to l0.1))).
asimpl. f_equal. fext. case. asimpl. rewrite /= H2.  done. intros. asimpl. simpl in *. done.
intros. rewrite /= -x. done. intro. intros. destruct x1,x2;try done.  f_equal. simpl in *. inversion H1. done. 
rewrite project_subst in H1. move : H1. asimpl. rewrite /= H2. intros. 
have:  [eEEnd .: var >> project^~ (ptcp_to  l0.1)] = [eEEnd .: ids]. fext. case;try done. intros.
rewrite x in H1. 
clear x.  apply estep_cont in H1 as HH. exfalso. apply : MUE_no_step. apply : MUE1. have: ~ eguarded 0 (project g0 (ptcp_to l0.1)).  lia. intros. apply : x. 2 : {  eapply H1. } simpl in *. done.

intro. intros. destruct x1,x2. done. simpl in *. done. simpl in *. done. f_equal. simpl in *. inversion H1.  done.
Qed.



Lemma unfeq_refl : forall e, econtractive2 e -> unfeq e e.
Proof.
intros. funelim (unfeq e e); try done; try rewrite -Heqcall.  inversion H0. lia. 
inversion H1. subst. rewrite !eqxx /=.  apply H. simpl in *. done. f_equal. done.
inversion H1. subst. rewrite !eqxx /=. clear Heqcall H1. elim : es0 H H0 . simpl in *.  simp foldIn. simpl in *.  
intros. simp foldIn. simpl in *. simp list_eq2. split_and. apply : H0. 4 : {  f_equal.   } auto.  auto. done.  done.  apply H.  

intros.  apply : H0. 4 : {   eauto. }   auto.  auto.  done. done. done.
rewrite /= eqxx. done.
clear Heq.
rewrite  H in e0. done. 
Qed.

(*Lemma unfeq2_refl : forall e, econtractive2 e -> unfeq2 e e.
Proof.
intros. rewrite /unfeq2. rewrite unfeq_refl. done.
done.
Qed. *)





Lemma project_tw0 : forall g p0 p1, lpreds ([::apred;spred;ppred;npred p0;npred p1]) g -> project g p0 = project g p1.  
Proof.
elim; rewrite /=;intros;try done. 

erewrite H;eauto. cc. 
list_lpreds [::3;4] H0. rewrite /= !inE. split_and.
rewrite (negbTE H3) (negbTE H4) (negbTE H6) (negbTE H7). apply H. cc.
list_lpreds [::3;4] H0. rewrite /= !inE. split_and.
rewrite (negbTE H3) (negbTE H4) (negbTE H6) (negbTE H7) !match_n.  apply H. cc. cc. 
Qed.




Lemma project_predP_aux : forall a gs p i, lpreds rec_pred (GBranch a gs) ->
p \notin a -> i < size gs  -> unfeq (project (nth GEnd gs 0) p) (project (nth GEnd gs i) p).
Proof. 
intros. have : project_pred (GBranch a gs) by cc. 
rewrite /=. split_and. move : H2. move/allP=>Hall. have : (nth GEnd gs i) \in gs by cc. 
move/Hall=> HH.  rewrite /= big_map in HH.

destruct (p \in (fresh (a `|` \bigcup_(j <- gs) ptcps j) |` (a `|` \bigcup_(j <- gs) ptcps j) `\` a)) eqn : Heqn.
apply (allP HH). done.

 rewrite !(@project_tw0 _ p (fresh (a `|` \bigcup_(j <- gs) ptcps j) )).

unlock lpreds in H. rewrite /preds in H. simpl in *. split_and. 
apply (allP HH).

rewrite !inE. done. 
unlock lpreds in H. rewrite /preds in H. simpl in *. split_and. 
unlock lpreds. rewrite /preds. simpl in *. split_and. 
apply (allP H9). apply/mem_nth.  done. apply (allP H8).  apply mem_nth. done.
apply (allP H7). cc. rewrite /npred.
move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H11) (negbTE H12) /= in H10. move : H10. move/bigfcupP=>HH'.  apply/negP. intro. apply HH'. exists (nth GEnd gs i). split_and. cc. 
done. 

move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H11) (negbTE H12) /= in H10. move : H10. move/bigfcupP=>HH'.  rewrite /npred. 
rewrite /fresh.  destruct (atom_fresh_for_list (([fset ptcp_from a; ptcp_to a] `|` \bigcup_(j <- gs) ptcps j))) eqn : Heqn. 
rewrite Heqn. apply/negP. intro. apply n. rewrite !inE. apply/orP. right. rewrite big_exists. apply/hasP. 
exists (nth GEnd gs i). cc. done.

unlock lpreds in H. rewrite /preds in H. simpl in *. split_and. 
unlock lpreds. rewrite /preds. simpl in *. split_and. 
apply (allP H9). apply/mem_nth.  done. apply (allP H8).  apply mem_nth. done.
apply (allP H7). cc. rewrite /npred.
move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H11) (negbTE H12) /= in H10. move : H10. move/bigfcupP=>HH'.  apply/negP. intro. apply HH'. exists (nth GEnd gs 0). split_and. cc. 
done. 

move : Heqn. move/negP/negP. rewrite /= !inE. split_and.  rewrite !inE in H0.  split_and.  rewrite (negbTE H11) (negbTE H12) /= in H10. move : H10. move/bigfcupP=>HH'.  rewrite /npred. 
rewrite /fresh.  destruct (atom_fresh_for_list (([fset ptcp_from a; ptcp_to a] `|` \bigcup_(j <- gs) ptcps j))) eqn : Heqn. 
rewrite Heqn. apply/negP. intro. apply n. rewrite !inE. apply/orP. right. rewrite big_exists. apply/hasP. 
exists (nth GEnd gs 0). cc. done.
Qed.

(*Lemma project_predP_aux2 : forall a gs p i n, lpreds rec_pred (GBranch a gs) ->
p \notin a -> i < size gs  ->  esize (project (nth GEnd gs 0) p) * esize (project (nth GEnd gs i) p) <= n -> unfeq n (project (nth GEnd gs 0) p) (project (nth GEnd gs i) p).
Proof. 
intros.*) 

Lemma unfeq_unf : forall e e', econtractive2 (ERec e) -> unfeq (e [e (ERec e)..]) e' ->
  unfeq (ERec e) e'.
Proof.
intros. funelim (unfeq (ERec e) e');try done. 
rewrite -Heqcall. inversion H2.  subst.  rewrite /= H1.  lia. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
Qed.

(*


Lemma unfeq_unf2 : forall e e', econtractive2 (ERec e) ->  unfeq (ERec e) e' -> unfeq (e [e (ERec e)..]) e'.
Proof.
intros. funelim (unfeq (ERec e) e');try done. 
inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.

inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.


inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e1.
done.


inversion H2. subst. rewrite /= Heqcall.   done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.

inversion H3. subst. rewrite -Heqcall in H2. apply H.  
done. rewrite /= -Heqcall.  done. 
f_equal.
funelim (unfeq (ERec e0) (ERec e1'));try done.  rewrite /= -Heqcall0.

 simp unfeq.
funelim (unfeq_unfold_clause_5 e0 (Sumbool.sumbool_of_bool (econtractive2 (ERec e0))) e1').
  have : econtractive2 (ERec e0) = true.  done. intros.
(*edestruct (econtractive2 (ERec e0)).*)
 Set Printing All. 
rewrite /Sumbool.sumbool_of_bool. 
rewrite x.  Set Printing All. setoid_rewrite x.move=>->.

setoid_rewrite H1.

destruct (orP H2). apply H. done.
funelim (unfeq (ERec e0) (ERec e1'));try done. 
  simp unfeq. rewrite /= H1.   simpl in *. simpl in *. done. done. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done

inv

rewrite Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
rewrite -Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e1.
done.
rewrite -Heqcall. inversion H2.  done.  
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
rewrite -Heqcall. inversion H3.  rewrite  H2. lia. 
simpl in *. split_and. clear Heq. inversion H1. subst. rewrite /= H2 H3 in e0.
done.
Qed.*)


(*Lemma step_test_end : forall g l g' p, step g l g' -> project g p = EEnd -> project g' p = EEnd.
Proof.
move => g l g' p. elim. 
- intros. simpl in *. move : H0. case_if.  done. case_if. done. done. 
- intros. simpl in *. move : H1. case_if.  done. case_if. done. rewrite /= match_n. intros.  rewrite /= -H3. symmetry. 
 suff :  unfeq  (project (nth GEnd gs 0) p) (project (nth GEnd gs n) p). rewrite /= H3.
  funelim ( unfeq EEnd (project (nth GEnd gs n) p));try done.
  rewrite /= -Heqcall. done.
 rewrite /= -Heqcall. done.
rewrite /= -Heqcall. done.

rewrite /= -Heqcall. done.

apply : project_predP_aux. unlock lpreds.  rewrite /gpred in H. unlock preds in H. simpl in *. split_and. eauto. done. 
rewrite /= !inE. split_and.  rewrite /= H1. done. rewrite /= H2. done. done. 
- intros. simpl in *. move :H3.  case_if.  done. case_if.  done. done.
- intros. simpl in *. move :H4.   case_if.  done. case_if.  done.  rewrite /= !match_n.  intros. 
  move : H2.  move/forallzipP=>HH. simpl in *. apply : HH.  done. cc. eauto.   

- intros. simpl in *. move : H2. case_if. done. move => _. apply H1. rewrite /= project_subst. asimpl. 
  simpl in *. rewrite /= H2. have : (EEnd .: (var >> project^~ p)) = (EEnd .: ids). fext. case.  done. simpl in *.
  intros.  done. move=>->.  done.

 qqq
rewrite /= -H6.  symmetry.
   suff :  unfeq  (project (nth GEnd gs 0) p) (project (nth GEnd gs n) p). rewrite /= H3.
  funelim ( unfeq EEnd (project (nth GEnd gs n) p));try done.
  rewrite /= -Heqcall. done.
 rewrite /= -Heqcall. done.
rewrite /= -Heqcall. done.

rewrite /= -Heqcall. done.

apply : project_predP_aux. unlock lpreds.  rewrite /gpred in H. unlock preds in H. simpl in *. split_and. eauto. done. 
rewrite /= !inE. split_and.  rewrite /= H1. done. rewrite /= H2. done. done. 

done.
-

lia. 
unloce 
rewrite /= -Heqcall. done.
 simp unfeq. 
 suff : 
Check project_predP_aux.
destruct gs. simpl in *. done. case : n . zdone.
*)

Lemma unfeq_end e : unfeq EEnd e = is_mue e.
Proof.
intros. funelim (unfeq EEnd e);try done. 
Qed. 


Lemma is_mue_fset0 : forall e,  is_mue e -> endpoint_fv e = fset0.
Proof.
elim;intros.
simpl in *. done. 
done.
simpl in *. rewrite /= H. apply/fsetP=>k. 
apply Bool.eq_true_iff_eq. split.  move/imfsetP.  case.  simpl in *. intros. rewrite /= inE in p. done.
rewrite /= inE. done.
done.
simpl in *. done.
simpl in *. done.
Qed.

Lemma subst_fset0 : forall e sigma, (forall n, n \in endpoint_fv e -> sigma n = EVar n) -> e [e sigma] = e.
Proof.
elim;intros;simpl in *. apply H. rewrite /= inE. done. done. 
asimpl.  f_equal. apply H.  case. simpl in *. done. intros. simpl in *. asimpl. 
rewrite /= H0.  simpl in *. done.
apply/imfsetP. simpl in *. exists n.+1. rewrite /= !inE.  split_and. done. 
f_equal. apply H.  done.
f_equal. induction l.  done. simpl in *. f_equal. apply H.  done. intros. apply H0.
rewrite big_cons inE. rewrite /= H1. lia. apply IHl.  intros. apply H. rewrite /= inE H1. lia. done. 
intros. apply H0. rewrite big_cons inE H1.   lia.
Qed.

Lemma is_mue_no_subst : forall e sigma, is_mue e -> e [e sigma] = e.
Proof. intros. apply subst_fset0. intros. rewrite /= is_mue_fset0 in H0. rewrite /= inE in H0.  done.
done.
Qed.


Lemma is_mue1 : forall e0, is_mue e0 -> is_mue ([e(ERec e0)..] e0).
Proof.
intros. rewrite subst_fset0. done.
intros.  rewrite /= is_mue_fset0 in H0.  rewrite /= inE in H0.  done. done.
Qed.

Hint Resolve is_mue1 is_mue_no_subst.

Ltac case_sum := match goal with 
(*                   | [ H : (_ && _) = true  |- _ ] => destruct (andP H);clear H*)
                   |  |- context[Sumbool.sumbool_of_bool ?b ] => destruct  (Sumbool.sumbool_of_bool b )
                  end;simpl in *;try done.

Notation isnt_rec e := (if e is ERec _ then false else true).

Lemma unf_not_rec : forall e0 e1, unfeq (ERec e0) e1 -> isnt_rec e1 -> unfeq (e0 [e (ERec e0)..]) e1.
Proof.
intros. destruct e1; try done.  
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
move : H. simp unfeq. case_sum.
Qed.

(*Lemma is_mue_unfeq1 : forall e0 e1, is_mue e0 -> unfeq e0 e1 -> unfeq EEnd e1.
roof.
elim;try done;intros.
destruct (isnt_rec e1) eqn :Heqn. apply unf_not_rec in H1;try done. rewrite /= is_mue_no_subst in H1.    apply H.  
 done. done. done. apply H.  done. destruct e1; try done. 
move : H1. simp unfeq. case_sum. 
move/orP.  case.  apply H. done. simpl in *. done. rewrite /= is_mue_no_subst.

rewrite /= unfeq_end.  done. rewrite /= unfeq_end.  done.
simp unfeq. move : H1.  simp unfeq. case_sum. move/orP. case.  intros. 
case_sum.  

case_sum.  /orP.  
one.  done.
move : H1.  simp unfeq. case_sum. move/orP. case. 
Urewrite /= is_mue_fset0 in H1. 
simpl in *. 
rewrite /= subst_fset0 in H1.  apply H.  done. done. intros.  rewrite /= subst_fset0 in H1. 
destruct e1;try done. 

simpl in *. apply H. done. move : H1. intros.   
funelim (unfeq e e1);try done. 
move : H1. simp unfeq . simpl in *. destruct e;try done. simpl in *.
move/orP. case. rewrite /= unfeq_end. done. rewrite /= unfeq_end.  done.
rewrite /= -Heqcall. rewrite /= subst_fset0.
 apply H.  done. move : H1.  simp unfeq.  simpl in *.
case : e;try done. 
destruct e1. 
destruct (eguarded 0 e && econtractive2 e) eqn:Heqn. 
simp unfeq. rewrite /=. rewrite /= {2}Heqn.
pply unfeq_unf in H1.  *)

Lemma is_mue_guarded : forall e i, is_mue e -> eguarded i e.
Proof.
elim;intros;try done.  simpl in *. apply H. done.
Qed. 

Lemma is_mue_cont : forall e, is_mue e -> econtractive2 e.
Proof.
elim;intros;try done. simpl in *. rewrite /= is_mue_guarded //=. auto.
Qed.

Lemma both_is_mue : forall e0 e1, is_mue e0 -> is_mue e1 -> unfeq e0 e1.
Proof.
elim;try done;intros. destruct e1;try done. simp unfeq. case_sum. rewrite /= is_mue_no_subst. apply H.  done. done.
done. rewrite /= is_mue_guarded in e0. rewrite /= is_mue_cont in e0.  done.

done. done.
simp unfeq. case_sum.  rewrite /=  is_mue_no_subst. rewrite /= H.  lia.  done. done. done.
rewrite /= is_mue_guarded in e0. rewrite /= is_mue_cont in e0.  done. done. done.
Qed. 

Lemma is_mue_unfeq : forall e0 e1, is_mue e0 -> unfeq e0 e1 -> is_mue e1.
Proof.
elim;try done;intros.
simpl in *. apply H. done. 
move : H1.  simp unfeq.  case_sum.  rewrite /= is_mue_no_subst //=.
move/orP.    case.  move/eqP=><-.  apply both_is_mue.  done. done. done.
Qed.


Lemma list_eq_trans : forall l0 l1 l2 (f : endpoint -> endpoint -> bool) ,  (forall e0 e1, In e0 l0 -> In e1 l1 -> forall e2 : endpoint, f e0 e1 -> f e1 e2 -> f e0 e2) -> list_eq f l0 l1 -> list_eq f l1 l2 -> list_eq f l0 l2.
Proof.                            
elim. case.  case.  done. done. move => a l l2 f.  done.
move => a l IH.  case.  done.
move => a0 l0. case.  done.
move => a1 l1 f IH2.  simpl in *. split_and.  apply : IH2.  eauto.  eauto.  done. done. apply : IH. all   : eauto.  
Qed. 

Lemma list_eq_trans2 : forall l0 l1 l2 (f : endpoint -> endpoint -> bool) ,  (forall e0 e2, In e0 l0 -> In e2 l2 -> forall e1 : endpoint, f e0 e1 -> f e1 e2 -> f e0 e2) -> list_eq f l0 l1 -> list_eq f l1 l2 -> list_eq f l0 l2.
Proof.                            
elim. case.  case.  done. done. move => a l l2 f.  done.
move => a l IH.  case.  done.
move => a0 l0. case.  done.
move => a1 l1 f IH2.  simpl in *. split_and.  apply : IH2.  eauto.  eauto.  eauto. done. apply : IH. all   : eauto.  
Qed. 


(*Lemma unfeq_rec_left : forall e e', econtractive2 (ERec e) -> unfeq (ERec e) e' = (if e' is ERec e'' then unfeq e e'' else false) || unfeq (e [e (ERec e)..]) e'. 
Proof.
intros. destruct e';simpl in *;try done;simp unfeq;case_sum.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. done.
rewrite /= H in e0. f_eql done.
Qed.*)



(*Lemma unfeq_in_rec : forall e0 e1 e, unfeq e0 e1 ->  unfeq (ERec e0) e -> unfeq (ERec e1) e.
Proof.
intros. move : H0.  rewrite /= !unfeq_rec_left. 
destruct (isnt_rec e) eqn : Heqn. intros. 
have :  unfeq ([e(ERec e0)..] e0) e. destruct e; try done. 
intros. 


move => v. 
 destru
rewrite /=tftf
 funelim (unfeq e0 e1);try done.
- have : n0 = n1.   move : H. simp unfeq. lia. intros. subst. done. 
-  apply both_is_mue. simpl in *. rewrite /= -unfeq_end.  done.
  move : H0. rewrite /= unfeq_rec_left.    
  destruct (isnt_rec e2) eqn : Heqn. intros.    have : unfeq EEnd e2. 
  destruct e2 ;try done.   rewrite unfeq_end.  done. destruct e2; try done. 
  move/orP.  case.  rewrite /= unfeq_end.  done. simpl in *. rewrite unfeq_end.  done.
  simpl in *. done.
- 
  
simp unfeq.  case_sum. 


simp

move/eqP=><-. done. apply : H. eauto. done. f_equal. rewrite /= -Heqcall.  move : H1.  simp unfeq. case_sum.  inversion H2. subst. eapply H in H0. 
  3 : {  f_equal. 

done.

move => e0 e1 e H. funelim (unfeq e0 e1).
- destruct e;simp unfeq; case_sum;try done.
*)
Lemma unfeq_trans : forall e0 e1 e2, econtractive2 e0 ->   unfeq e0 e1 -> unfeq e1 e2 -> unfeq e0 e2.
Proof.
intros.  funelim (unfeq e0 e2).
- simp unfeq. move : H0 H1. destruct e1; simp unfeq;try done.  lia. 
- simp unfeq. move : H0 H1. destruct e1; simp unfeq;try done.  
- all : try solve [move : H0 H1; destruct e1; simp unfeq ; done].  
- simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- move : H0.  simp unfeq. intros.  simp unfeq. apply : is_mue_unfeq. eauto. done.
-  simp unfeq. move : H1 H2. destruct e1; simp unfeq;try done.  
  split_and. rewrite /= (eqP H2) (eqP H3) //=.   
  rewrite /= (eqP H9) (eqP H6) //=. rewrite /= (eqP H8) (eqP H5) //=.
  apply : H. simpl in *. done.  eauto.  simpl in *. done.
-  simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- simp unfeq. move : H1 H2. destruct e1; simp unfeq;try done.  
  split_and. rewrite /= (eqP H1) (eqP H2) //=.   
  rewrite /= (eqP H7) (eqP H5) //=. rewrite /= list_eqP. rewrite /= list_eqP in H6. 
  rewrite /= list_eqP in H4. apply : list_eq_trans2.  2 : { eauto. } 2 : {  eauto. }
  intros. apply : H. eauto. eauto. 
  simpl in *. apply (allP H0). apply/inP. done. eauto. done. 
  f_equal.  done.
- simp unfeq. move : H0 H1. destruct e2; simp unfeq;try done.  
- rewrite /= -Heqcall. move :  H1.  simp unfeq.  case_sum. 
  move/orP. case. move/eqP=> HH.   subst. 
  move : H2. simp unfeq. case_sum. intros. erewrite H. lia. apply econtractive2_subst.  
  split_and.  case.  done. done.
  eauto.  done.
  clear Heq.   rewrite H in e0. done.
Qed.


(*Lemma MUE_imp : forall e, MUE e -> is_mue e.
Proof.
move => e. elim. done. simpl in *. intros. 
rewrite /= is_mue_no_subst in H0.  Print MUE. done. inversion H. done.*)

Lemma is_mue_subst : forall e i sigma, eguarded i e = false -> sigma i = EEnd -> is_mue e [e sigma].
Proof.
elim;rewrite /=;intros.
have : n = i.  lia.  move=>->.  rewrite /= H0.  done.
done. asimpl.  apply : H.  eauto.  simpl in *. rewrite /funcomp.  rewrite /= H1. simpl in *.
done.
done.
done.
Qed. 


Lemma step_test3 : forall g l g' p, step g l g' ->p \notin l.1 ->
 unfeq (project g p) (project g' p).
Proof. 
move => g l g' p H. elim : H p;intros.
- simpl in *.
  rewrite !inE in H0. split_and.  rewrite (negbTE H1) (negbTE H2). rewrite unfeq_refl. done. apply cont_project. 
  simpl in *.
  rewrite !inE in H1.  split_and. rewrite (negbTE H2) (negbTE H3) match_n.  apply : project_predP_aux.  rewrite /gpred in H.  unlock preds in H. unlock lpreds.  simpl in *. split_and; eauto. 
  rewrite /= !inE. split_and. done. 
 
- simpl.  rifliad.   simp unfeq. rewrite /= !eqxx /=.  apply H1. done. 
  simp unfeq. rewrite /= !eqxx /=.  apply H1. done. apply H1. done.

- simpl.  rifliad. simp unfeq. rewrite /= !eqxx /=.  
  move : H2. clear H H1 H3 H5. rewrite /= list_eqP.   elim : gs gs' H0 H4. destruct gs'. simpl in *. intros. done. 
  done. intros. destruct gs'.  done. simpl in *. split_and. inversion H2.    
  simpl in *.   apply H5. done. 
  apply H.  lia. done. inversion H2. done.
- simp unfeq. rewrite /= !eqxx /=. rewrite /= list_eqP.  
  move : H2. clear H H1 H3 H5.  elim : gs gs' H0 H4. destruct gs'. simpl in *. intros. done. 
  done. intros. destruct gs'.  done. simpl in *. split_and. inversion H2.    
  simpl in *. apply H5.  done.
  apply H.  lia. done. inversion H2. done. 
- rewrite /= ! match_n. move : H2. 
  simpl in *. move/forallzipP=> Hzip. simpl in *. apply Hzip. done. cc. done. apply H1 in H2.
  simpl in *. case_if. 
 * rewrite project_subst in H2. move : H2.  asimpl. simpl in *.  rewrite /= H3.
   have :  ((ERec (project g0 p)) .: var >> project^~ p) = ((ERec (project g0 p)) .: ids).
   fext. case.  simpl in *. done. simpl in *. intros.  done. move =>->. intros.
   apply unfeq_unf.  simpl in *. rewrite H3 /=.  apply cont_project. done.
  intro. destruct x1.  case. simpl. done.  simpl. done. 
   simpl. intros. destruct x2. simpl in H2. done. simpl in H2. inversion H2. subst. done. 
  have : project (GRec g0) p = EEnd. simpl in *. rewrite /= H3.  done.
  intros. have : step (GRec g0) l0 g'0. constructor. done. done. intros.
simpl in H2. rewrite project_subst in H2. move : H2. asimpl. rewrite /= H3. intros. 

have:  [eEEnd .: var >> project^~ p] = [eEEnd .: ids]. fext. case;try done. intros.
rewrite x1 in H2. 
 apply : unfeq_trans.  done. 2 : { eauto. }
 rewrite /= unfeq_end. apply : is_mue_subst. eauto.  done.
 intro. intros.   destruct x1,x2; try (simpl in * ; done). f_equal. inversion H2. done. 
Qed.

(*Operational correspondance, completeness direction*)
Lemma harmony1 : forall g l g' S,  step g l g' -> l.1 `<=` S -> 
 EnvStep (projmap S g) l (projmap S g').
Proof.
intros.
have :  projmap S g =  (projmap S g).[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g (ptcp_from l.1)].[ptcp_to l.1 <- project g (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H2). 
by rewrite (eqP H3). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H2. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H3 HH. by rewrite mapf_if H1.
exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. rewrite fnd_rem1 H2 fnd_rem1 H3. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H1. done. 
move=>->.

have :  projmap S g' =  (projmap S g').[~ptcp_from l.1].[~ptcp_to l.1].[ptcp_from l.1 <- project g' (ptcp_from l.1)].[ptcp_to l.1 <- project g' (ptcp_to l.1)]. apply/fmapP=>k. rewrite !mapf_if !fnd_set. rifliad. by rewrite (eqP H2). 
by rewrite (eqP H3). Check setf_rem1. Search _ (_.[~_].[? _]). rewrite fnd_rem1 H2. have : ~~false = true by lia. move=>HH. rewrite HH. 
rewrite fnd_rem1 H3 HH. by rewrite mapf_if H1.
exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. exfalso. apply/negP. apply (negbT H1). apply : (fsubset_in). eauto. rewrite !inE H2. lia. rewrite fnd_rem1 H2 fnd_rem1 H3. have : ~~false = true by lia. move => ->. 
rewrite mapf_if H1. done. 
move=>->.
constructor. 
apply step_test. done. apply step_test2. done.
(*apply step_test2. done. *)
by rewrite /projmap /=.
move => p e e'. rewrite !fnd_rem1.  destruct (p != ptcp_to l.1) eqn:Heqn.    destruct (p != ptcp_from l.1) eqn : Heqn2.  intros. 
move : H1. move/[dup]. intro. 
move : H2. rewrite /projmap !mapf_if. rifliad. move=>[] HH [] HH0. rewrite /= -HH -HH0.  apply : step_test3. eauto. rewrite !inE . rewrite /= Heqn Heqn2. done. 
case. move=>->.  move : H3. rewrite mapf_if H1. done. done. done.
Qed.

Check subst_fset0. 

Lemma ren_fset0
     : forall (e : endpoint) sigma,
       (forall n : nat_choiceType, n \in endpoint_fv e -> sigma n = n) ->  e ⟨e sigma ⟩ = e.
Proof.
elim;intros;asimpl.   
rewrite /= H. done. rewrite /= inE. done.
done.
f_equal.  asimpl. apply H. case. done. intros. simpl in *. rewrite /funcomp. rewrite /= H0. done. 
apply/imfsetP.  simpl in *. exists n.+1.  rewrite inE H1. done. done.
f_equal.  apply H.  done.
f_equal. induction l.  done.  simpl in *. f_equal. apply H. done. 
intros.  apply H0.  rewrite /= big_cons inE H1.  done.
apply IHl.  intros.  apply H.  rewrite /= inE H1. lia. done. 
intros.  apply H0.  rewrite /= big_cons inE H1. lia. 
Qed.



(*Lemma subst_step0 : forall e e2 d c vn, econtractive2 (ERec e) -> Estep (ERec e) (d,c,vn) e2 -> exists e', e2 = e' [e (ERec e).. ].
Proof.
intros.  inversion H0.  subst. 
elim;intros. 
-  simpl in *. inversion H0. subst. destruct n.  done. simpl in *. inversion H3. 
- inversion H0.  simpl in *.  subst.  inversion H3. 
- simpl in *. split_and.  have : exists e', e2 = e' [e (ERec e)..]. apply : H. split_and. *)

(*Lemma in2 :
  forall (g : endpoint) [i : nat] [sigma : fin -> endpoint], i \in endpoint_fv ([esigma] g) ->
  (exists n : fin, i \in endpoint_fv (sigma n)).
Proof.
elim;simpl in *;intros. 
exists n. done.
rewrite /= inE in H.  done.
move :H0.  move/imfsetP.  simpl in *. case.  move => x. rewrite /= inE. asimpl.  split_and. subst. 
apply H in H0. destruct H0.  exists x0. destruct x0. simpl in *. rewrite /= inE in H0.  lia. simpl in *. done.
mointros. destruct (i \in endpoint_fv (sigma n)) eqn :Heqn.  done.
exfalso. apply/negP. apply/inotine2. 2 : {  intros.  instantiate (2 := i).  instantiate (1 :=)  erewrite Heqn. 
elim;intros;simpl in *. 
*)
Print endpoint_fv.
(*
Ltac split_eq := apply Bool.eq_true_iff_eq;split.
Notation im := imfsetP.
Lemma map_fv0 : forall e sigma, endpoint_fv (e ⟨e sigma⟩) = [fset sigma n | n in endpoint_fv e].  
Proof.
elim;intros;rewrite /=.
apply/fsetP=> k. rewrite /= inE. split_eq. move/eqP. move=>->. 
apply/imfsetP. simpl in *. exists n.  rewrite /= inE.  done. done.
move/imfsetP=>[] x.  rewrite /= inE. move/eqP=>->.  lia. 
apply/fsetP=>k. split_eq.  rewrite /= inE.  done.
move/imfsetP=>[]x. simpl in *.  rewrite inE.  done. asimpl. 
rewrite /= H. asimpl. 
apply/fsetP=>k.  split_eq. move/imfsetP=>[] x. rewrite /= inE. split_and. 
move: H0.  move/im=>[] x'. simpl in *. intros.  subst.  destruct x'.  done. simpl in *. 

apply/im. simpl in *. exists x'. apply/im.  simpl in *. exists x'.+1. rewrite /= inE.  split_and.  done.
done. move/im=> [] x.  rewrite /=.  move/im=> [] x'.  rewrite /= inE. split_and.  subst. 
apply/im.  simpl in *. exists (sigma x'). rewrite /= inE. split_and. 
apply Bool.ef

 destruct (eqVneq k (sigma n)). apply/imfsetP. 
Lemma map_fv : forall e sigma, endpoint_fv (e [e sigma]) = \bigcup_(i <- endpoint_fv e ) (endpoint_fv (sigma i)).  
Proof.
elim;intros;rewrite /=.  apply/fsetP=>k.  rewrite /= big_exists.  apply Bool.eq_true_iff_eq.  
split.  intros. apply/hasP.  exists n.  rewrite /= inE.  done. done.
move/hasP=>[]. intros. rewrite /= inE in p. rewrite -(eqP p) q. done.
rewrite big_nil.  done. asimpl.  rewrite /= H. 
apply/fsetP=>k. apply Bool.eq_true_iff_eq.  split.  move/imfsetP=>[] x /=. rewrite /= inE.  split_and. 
move : H0. rewrite /= big_exists. move/hasP=>[]. intros. 
rewrite big_exists.    apply/hasP. destruct x eqn:Heqn. done. subst. simpl in *.
exists x0.-1. 2 : { destruct x0.  simpl in *.  rewrite /= inE in q0.  lia. simpl in *.
 move : q0.  asimpl. intros. Search _ (_ \in endpoint_fv (_ ⟨e _ ⟩)).

apply/imfsetP. rewrite /=. exists x0.+2. rewrite /= inE.  split_and. 
rewrite inE. zn

rewrite /= big_cons. 



[fset sigma n | n in endpoint_fv e].*)

Print endpoint. 
Fixpoint not_empt e :=
match e with
| ERec e' => not_empt e'
| EMsg _ _ _ _ => true 
| EBranch _ _ _ => true
| _ => false 
end. 





Lemma subst_step1 : forall e e2 sigma d c vn, econtractive2 e -> (forall v, eguarded v e) ->  Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
move => e e2 sigma d c vn H0 H1 HH. remember (e [e sigma]). elim : HH e Heqe0 H0 H1;intros.  
destruct e;simpl in *. specialize H1 with n. lia. done. 
exists e.  inversion Heqe0.  done. 
all : try done. 
destruct e;simpl in *. specialize H4 with n. lia. done. 
inversion Heqe0.  subst. edestruct H1. eauto. done. apply H3 in H1.  simpl in *. apply H1 in H8. 
exists e.  inversion Heqe0.  done. 
all : try done. 
elim;intros.
- simpl in *. apply : H. eauto. 
- simpl in *. inversion H0. 
- simpl in *. move : H1. asimpl. intros. inversion H1. subst.
  move : H4. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. intros. 
  destruct v.  simpl in *. have : e1 = e2.  admit. 
  intros.  subst. apply : H. intros. 
destruct l. destruct p.  

apply H in H2.  
  inversion H2.  subst. move : H6.  asimpl. 
  rewrite /= H3. 
  exists (x [eERec ([eEVar 0 .: EVar >> ⟨e ↑ ⟩] e) .: ids]). 

  asimpl.
  f_equal.   

Lemma subst_step1 : forall e e2 sigma d c vn, (forall v e1, Estep (sigma v) (d,c,vn) e1 -> exists e', e1 = e' [e sigma] ) ->  Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
elim;intros.
- simpl in *. apply : H. eauto. 
- simpl in *. inversion H0. 
- simpl in *. move : H1. asimpl. intros. inversion H1. subst.
  move : H4. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. intros. 
  destruct v.  simpl in *. have : e1 = e2.  admit. 
  intros.  subst. apply : H. intros. 
destruct l. destruct p.  

apply H in H2.  
  inversion H2.  subst. move : H6.  asimpl. 
  rewrite /= H3. 
  exists (x [eERec ([eEVar 0 .: EVar >> ⟨e ↑ ⟩] e) .: ids]). 

  asimpl.
  f_equal.   
- simpl in *.  inversion H2; subst. exists e.  done. 
  destruct (not_empt e) eqn : Heqn.  edestruct H. done. eauto. eauto. subst. 
  exists (EMsg Sd c v x).  done. destruct e;simpl in *. 
apply H in Heqn. apply 
simpl in *. iapply : H.  done. 
f_equal. f_equal. apply inj_rem4'. intros. 
  case : v H4. simpl in *. done. intros.  simpl in *.
  rewrite /funcomp. have : endpoint_fv (sigma n) = fset0.    apply H1. 
  apply/imfsetP.  simpl in *. exists n.+1.  rewrite /= !inE H8.  done. done.
  intros. rewrite subst_fset0. rewrite ren_fset0. done.
  intros.    rewrite /= x0 in H9. rewrite /= inE in H9. done.
  intros. rewrite /= x0 inE in H9.  done.

 done.  specialize H1 with n.+1. 
  
move : H1. move/imfsetP.   rewrite /= inE.  Check imfsetP.  rewrite /=.
  apply inj_rem4'. intros. case: v H8.  simpl in *. intros. 
  f_equal. apply_i
a
  intros. 
f_equal.  f_equal. f_equal. f_equal.  f_equal. f_equal. Unset Printing Notations. 
done. intros. 
 

Lemma subst_step1 : forall e e2 sigma d c vn, econtractive2 e -> (forall v, v \in endpoint_fv e -> endpoint_fv (sigma v) = fset0) -> 
(endpoint_fv (e [e sigma]) = fset0) ->
(forall v, eguarded v e) -> Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ].
Proof.
elim;intros.
- simpl in *. specialize H2 with n.   rewrite /= eqxx in H2. done.
- simpl in *. inversion H3.
- simpl in *. split_and. move : H4. asimpl. intros. inversion H4. subst.
  move : H8. asimpl. have : sigma >> ssrfun.id = sigma. fext. intros. done. move =>->. 
  move/H=> HH.  edestruct HH. 
  done. intros. 
  destruct v.
  simpl in *. rewrite /= -H2. 
  apply/fsetP=> k. apply Bool.eq_true_iff_eq.  split. 
  move/imfsetP=>[] x.  rewrite /= !inE. split_and. simpl in *. subst. apply/imfsetP. simpl in *.
  exists x. rewrite /= inE H9. split_and. done.
  move/imfsetP=>[] x.  rewrite /= !inE. split_and. simpl in *. subst. apply/imfsetP. simpl in *.
  exists x. rewrite /= inE H9. split_and. done.

  simpl in *. rewrite /= H1.  done. apply/imfsetP.  simpl in *. exists v.+1.  rewrite /= inE H0. done. done. 
  move : H2. asimpl. intros. 
  
rewrite /= -H2. 
  apply/fsetP=>k. apply Bool.eq_true_iff_eq.  split. intros. asimpl. 
  apply/imfsetP.  simpl in *. exists k.+1.  rewrite /= inE. split_and. 
  2 : {  done. } 2 : { move/imfsetP. simpl in *. case.  move => x. rewrite /= inE. split_and. subst. 
  move : H0.  asimpl.  intros. destruct x.  done. simpl in *. 

rewrite /= H0.case.  move => x.  rewrite /= !inE. split_and. subst. 
  Search _ (endpoint_fv (_ [e _])). destruct x. done. exfalso.  
  
apply/negP. apply/inotine2. 3 : {  apply : H7.  }  intros. destruct n.  simpl in *. rewrite /= inE.  done.
  simpl in *. rewrite /funcomp.  rewrite ren_fset0. rewrite /= H1. rewrite  inE. done.
  apply/imfsetP. simpl in *. exists n.+1.  rewrite /= inE. split_and. 

Search _ (endpoint_fv _).
 subst. 
case. 

 rewrite inE. intros. 
admit. apply : H2. 
  destruct H0. rewrite /= H0. 
  exists (x [eERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: ids]). 

  split.  asimpl.
  f_equal.   f_equal. f_equal. apply inj_rem4'. intros. 
  case : v H8. simpl in *. done. intros.  simpl in *.
  rewrite /funcomp. have : endpoint_fv (sigma n) = fset0.    apply H1. 
  apply/imfsetP.  simpl in *. exists n.+1.  rewrite /= !inE H8.  done. done.
  intros. rewrite subst_fset0. rewrite ren_fset0. done.
  intros.    rewrite /= x0 in H9. rewrite /= inE in H9. done.
  intros. rewrite /= x0 inE in H9.  done.

 done.  specialize H1 with n.+1. 
  
move : H1. move/imfsetP.   rewrite /= inE.  Check imfsetP.  rewrite /=.
  apply inj_rem4'. intros. case: v H8.  simpl in *. intros. 
  f_equal. apply_i
a
  intros. 
f_equal.  f_equal. f_equal. f_equal.  f_equal. f_equal. Unset Printing Notations. 
done. intros. 
  have : exists e', e2 = e' [ERec ([eEVar 0 .: sigma >> ⟨e ↑ ⟩] e) .: sigma   
  apply : H.  done. 
  case.  done. intros.  apply H1.  apply/imfsetP. simpl in *. 
  exists n.+1. rewrite /= inE. split_and.  done. eauto. 
  move => []. intros. rewrite /= p. exists (x0 [e ERec ( (*sigma >> *) e [e ids]) .: ids]). 
  asimpl. f_equal.  
- apply : H.  simpl in *.  done. simpl in *. done.

f_equal.  f_equal. f_equal. f_equal. 
fmove/H. move => HH. apply : HH.  done. 
  inversion H2. subst. 
eapply HH in H4. 
  edestruct H4.  destruct H0. exists x. split.  eauto. constructor. admit.  
  intros. 
apply H. move/H.


Print Estep. 
Lemma subst_step : forall e e2 sigma d c vn, econtractive2 e -> (forall v, v \in endpoint_fv e -> eguarded v e) -> Estep (e [e sigma]) (d,c,vn) e2 -> exists e', e2 = e' [e sigma ] /\ Estep e (d,c,vn) e'.
Proof.
elim;intros.
- simpl in *. specialize H0 with n.  rewrite /= !inE in H0. exfalso. apply/negP. apply H0. done. done. 
- simpl in *. inversion H1.
- simpl in *. split_and. move : H2. asimpl. intros. 
  have : forall v, v \in endpoint_fv e -> eguarded v e.
  case.  done. intros.  apply H1.  apply/imfsetP. simpl in *. 
  exists n.+1. rewrite /= inE. split_and.  done. move/H. move => HH. eapply HH in H4. 
  edestruct H4.  destruct H0. exists x. split.  eauto. constructor. admit.  
  intros. 
apply H. move/H.


term+)

Print label. Check ch.
Locate "+". Print Estep.

Definition fLabel := ( dir * ptcp * ch * (value + nat))%type.

(*Parameter (f : fLabel). Check (f.1).*)
Definition fType := (gType * option (ptcp * ch * (value + nat)))%type.
Print step. 
Inductive HalfStep : fType -> fLabel -> fType -> Prop  :=
| HS1 a u g p c vn : ptcp_from a = p -> action_ch a = c -> inl u = vn -> 
   HalfStep (GMsg a u g, None) (Sd,p,c,vn) (GMsg a u g, Some (p,c,vn))
| HS2 a u g p0 p1 c vn : ptcp_from a = p0 -> ptcp_to a = p1 -> action_ch a = c -> inl u = vn -> 
   HalfStep (GMsg a u g, Some (p0,c,vn)) (Rd,p1,c,vn) (g, None)
| HS_async a u d g g' f f' p c vn: ptcp_to a <> p -> HalfStep (g,f) (d,p,c,vn) (g',f') ->  
   HalfStep (GMsg a u g,f) (d,p,c,vn) (GMsg a u g', f')
| HS3 a p c vn n gs : ptcp_from a = p -> action_ch a = c -> inr n = vn -> n < size gs -> 
   HalfStep (GBranch a gs, None) (Sd,p,c,vn) (GBranch a gs, Some (p,c,vn))
| HS4 a p0 p1 c vn n gs : ptcp_from a = p0 ->  ptcp_to a = p1 -> action_ch a = c -> inr n = vn ->
   HalfStep (GBranch a gs, Some (p0,c,vn)) (Rd,p1,c,vn) (nth GEnd gs n, None)
| HS5 a p f f' d c vn gs gs' : ptcp_to a <> p ->
   size gs = size gs' -> Forall (fun pp => HalfStep (pp.1,f) (d,p,c,vn)  (pp.2,f')) (zip gs gs') ->
   HalfStep (GBranch a gs, f) (d,p,c,vn) (GBranch a gs', f').
Print label. 

(*Lemma HalfP : forall gp l gp'' f  g g'' p0 c vn p1 d,
 HalfStep gp l gp'' -> gp = (g,None) -> l = (d,p0,c,vn) -> gp'' = (g'',f) ->  exists g', 
 HalfStep (g'',f) (Rd,p1,c,vn) (g',None) /\ step g (Action p0 p1 c,vn) g'.
Proof. 
move => gp l gp'' f g g'' p0 c vn p1 d. elim;intros. 
- inversion H2. inversion H3. inversion H4.  subst. 
*)

Ltac pinv := repeat (match goal with 
                   | [ H : (_,_) = (_,_) |- _ ] => inversion H;clear H
                  end);subst.

Print Estep. Print step. 

Lemma TestProj : forall g p0 c vn e, Estep (project g p0) (Sd,c,vn) e ->
  exists g' p1, project g' p0 = e /\ step g (Action p0 p1 c,vn) g'.
Proof.
move => g p0 c vn e HH.
remember (project g p0).  
remember (Sd,c,vn).
move : HH g c vn p0 Heqe0 Heqp.
elim;intros. 
pinv.  destruct g; simpl in *;try done. move : Heqe0.     case_if.  done. done.
move : Heqe0.  case_if;try done. case.  intros. subst. 
exists g ,(ptcp_to a).  split.  done. rewrite /= (eqP H0). 
have : Action (ptcp_from a) (ptcp_to a) (action_ch a) = a. destruct a.  done. 
move =>->. constructor. admit. 
case_if.  done. intros. exists g ,p0.  rewrite -Heqe0.

apply
Lemma TestProj : forall g p0 p1 c vn e e', Estep (project g p0) (Sd,c,vn) e -> Estep (project g p1) (Rd,c,vn) e' -> 
  exists g', project g' p0 = e /\ project g' p1 = e' /\  step g (Action p0 p1 c,vn) g'.
Proof.
move => g p0 p1 c vn e e' HH. 

remember (project g p1).  
remember (Sd,c,vn).
remember (Rd,c,vn).
move : HH e1 g p0 p1 c vn p2 e' Heqe0 Heqe1 Heqp Heqp2. 
elim. 
- intros.  pinv.
 remember (project g p1).    


as ident
Lemma HalfP : forall gp l0 gp'' l1 gp'  g g'' p0 c vn g' p1,
 HalfStep gp l0 gp'' ->  HalfStep gp'' l1 gp' -> gpred g ->
gp = (g,None) -> gp'' = (g'',Some (p0,c,vn)) -> gp' = (g',None) ->
l0 = (Sd,p0,c,vn) -> l1 = (Rd,p1,c,vn) ->  step g (Action p0 p1 c,vn) g'. 
Proof. 
move => gp l0 gp'' l1 gp' g g'' p0 c vn g' p1.  
elim. 
- intros. pinv. clear H15 H14 H13. 
  inversion H2.  subst. e

   move =>->. constructor. done.
   subst. apply GR3. done.

move => a u g0 p c0 vn0 H0 H1 H2 HH.
  remember ((GMsg a u g0, Some (p, c0, vn0))).
  move : HH a u g0 p c0 vn0 H0 H1 H2 Heqp2.
  elim;intros. 
 * pinv.
 * pinv.
   have : Action (ptcp_from a0) (ptcp_to a0) (action_ch a0) = a0. destruct a0.   done.
   move =>->. constructor. done.
 * pinv. apply : H1.  4 : {  f_equal.  apply GR3. done. 
  inversion Heqp.  
  inversion Heqp.  subst.  inversion H7. subst.  inversion H5. subst. 
  inversion Heqp2.  subst. 
  apply IHHalfStep.
induction H2.  inversion H7. subst. inversion H4. subst. inversion H5. subst. 
  inversion H2. 

   move =>->.  constructor. done.
 * subst. inversion 
done.

inversion Heqp. subst. clear Heqp. inversion H2. subst. 
  * Print step. 
constructor. 




induction H. 
Admitted. 

Parameter (p : fLabel). Check (p.1).



Definition projHalf g p (f : fLabel) e := Estep (project g p) (Sd,f.1.2,f.2) e.


Lemma harmony2_1 : forall e0 c vn e1 p, Estep e0 (Sd,c,vn) e1 -> exists g g', project g p = e0 /\ projHalf g p (p,c,vn) e1 /\
                                                                     HalfStep1 g (g',(p,c,vn)). 
Proof. Admitted.

Lemma harmony2_2 : forall e0 c vn e1 p, Estep e0 (Rd,c,vn) e1 -> exists g g', project g p = e0 /\ project g' p = e1 /\
                                                                     HalfStep2 (g,(p,c,vn)) (g',(p,c,vn)). 
Proof. Admitted.w


Lemma harmony2 : forall g l d  S,
 EnvStep (projmap S g) l d ->  exists g', projmap S g' = d /\ step g l g'.  
Proof.
intros. destruct H.  inversion H. subst. 
