From mathcomp Require Import all_ssreflect zify.
From Equations Require Import Equations.
From mathcomp Require Import finmap.
From Paco Require Import paco.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import Global_Syntax Inductive_Linearity Substitutions Predicates Structures Projection.

Let inE :=  Structures.inE.

Unset Elimination Schemes. 
Inductive Estep : endpoint ->  (dir * ch * (value + nat))  -> endpoint -> Prop :=
| estep_msg d c v e0  : Estep (EMsg d c v e0) (d,c, inl v) e0
| estep_msg_async d d2 vn c c' v e0 e0'  : (d = Sd \/ d2 = Sd) -> Estep e0 (d2,c,vn) e0' -> c <> c' -> 
                                        Estep (EMsg d c' v e0) (d2,c,vn) (EMsg d c' v e0')
| estep_branch n es d c   : n < size es -> Estep (EBranch d c es) (d,c, inr n) (nth EEnd es n)
| estep_branch_async es0 es1 vn d d2 c c'  : (d = Sd \/ d2 = Sd) -> size es0 = size es1 -> Forall (fun p =>  Estep p.1 (d2,c,vn) p.2) (zip es0 es1) -> c <> c' -> 
                                          Estep (EBranch d c' es0) (d2,c,vn) (EBranch d c' es1)
| estep_rec e l e1 e' : e =f= e1 -> Estep e1 l e' -> Estep e l e'.
Set Elimination Schemes.
Hint Constructors Estep.

Lemma Estep_ind
     : forall P : endpoint -> dir * ch * (value + nat) -> endpoint -> Prop,
       (forall (d : dir) (c : ch) (v : value) (e0 : endpoint), P (EMsg d c v e0) (d, c, inl v) e0) ->
       (forall (d d2 : dir) (vn : value + nat) (c c' : ch) (v : value) (e0 e0' : endpoint),(d = Sd \/ d2 = Sd) ->
        Estep e0 (d2, c, vn) e0' -> P e0 (d2, c, vn) e0' -> c <> c' -> P (EMsg d c' v e0) (d2, c, vn) (EMsg d c' v e0')) ->
       (forall (n : nat) (es : seq endpoint) (d : dir) (c : ch), n < size es -> P (EBranch d c es) (d, c, inr n) (nth EEnd es n)) ->
       (forall (es0 es1 : seq endpoint) (vn : value + nat) (d d2 : dir) (c c' : ch), (d = Sd \/ d2 = Sd) ->
        size es0 = size es1 ->
        Forall (fun p : endpoint * endpoint => Estep p.1 (d2, c, vn) p.2) (zip es0 es1) ->
        Forall (fun p : endpoint * endpoint => P p.1 (d2, c, vn) p.2) (zip es0 es1) ->
        c <> c' -> P (EBranch d c' es0) (d2, c, vn) (EBranch d c' es1)) ->
       (forall (e : endpoint) (l : dir * ch * (value + nat) ) (e1 e' : endpoint),
        e =f= e1 -> P e1 l e' -> P e l e') ->
       forall (e : endpoint) (p : dir * ch * (value + nat)) (e0 : endpoint), Estep e p e0 -> P e p e0.
Proof.
intros. move : e p e0 H4. fix IH 4;intros. destruct H4.
- apply H;auto.
- apply H0;auto.
- apply H1;auto.
- apply H2;auto. elim : H6;auto. 
- eapply H3. apply : H4. auto. 
Qed.


Inductive EnvStep : env -> label -> env -> Prop := 
| envstep_rule (Δ Δ' : env) e0 e1 e0' e1' l : Estep e0 (Sd,action_ch l.1,l.2) e0' ->  Estep e1 (Rd,action_ch l.1,l.2) e1' ->  
                           domf Δ = domf Δ' -> (forall p e e',  Δ.[? p] = Some e -> Δ'.[? p] = Some e' -> e =f= e') -> EnvStep Δ.[ptcp_from l.1 <- e0].[ptcp_to l.1 <- e1] l  Δ'.[ptcp_from l.1 <- e0'].[ptcp_to l.1 <- e1'].
Hint Constructors EnvStep.
Search _ (_.[_ <- _]).

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


Definition try_fnd (d : env) (p : ptcp) := if d.[? p] is Some e then e else EEnd.

Definition map_subst (i : nat) (d : env) g := [fmap x : (domf d) => subst_e i (try_fnd d (val x)) (project g (val x))]. 


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





Lemma projmap_subst : forall g0  g i S, lpreds [::bound] g -> projmap S (substitution i g0 g) = map_subst i (projmap S g0) g.
Proof.
intros. rewrite /projmap /map_subst. apply/fmapP=>k. rewrite !mapf_if. 
rewrite (@mapf_if _ _ _ (fun x =>  subst_e i (try_fnd ([fmap p => project g0 (val p)]) (x)) (project g (x)))) /=.
rifliad. f_equal. rewrite project_subst. rewrite /try_fnd. rewrite mapf_if H0. done. done. 
Qed.

Lemma ueqe_subst : forall e0 e1 e' n, (lpreds [::bounde]) e0 -> (lpreds [::bounde]) e1 -> e0 =f= e1 ->  e0[e e'//n] =f= e1[e e'//n].
Proof. pcofix CIH.  intros. punfold H2. ich H2;simpl;auto.  ich H.
pfold. constructor. right.  apply : CIH. cc. cc. nth_lpreds 0 H0. rewrite /bounde. by simpl. cc.  nth_lpreds 0 H1. rewrite  /bounde. simpl. eauto. done.
pfold. constructor. by rewrite !size_map.
have : (zip (map (fun e0' => (e0')[e e' // n]) gs)  (map (fun e0' => (e0')[e e' // n]) gs')) = map (fun p => (p.1[e e'//n ],p.2[e e'//n])) (zip gs gs'). clear H1 CIH H H0 H3. elim : gs gs'.  destruct gs'. done. by simpl.  destruct gs'. done.
simpl.  f_equal. apply H. move=>->. induction H3. constructor. rewrite /=. constructor. simpl. right. apply : CIH. cc. ich H0.
auto. 
rifliad. pfold. constructor. ich H. rewrite (eqP H0). right.
 rewrite -(@subst_e_nop (g[e ERec n g // n]) e' n). apply : CIH. rewrite -(eqP H0). done.
Search _ (efv (subst_e _ _ _)).  rewrite Substitutions.efv_subst. by rewrite /= !inE.
pfold. constructor. right. apply : CIH.
move : 
rewrite map_zip.
right. apply : CIH. move => e0 e1 e' n.

Instance traverse_project_pred_unf : forall g0 g1 i, {goal lpreds rec_pred g0} -> {goal lpreds ([::bound;project_pred]) g1} ->  {goal project_pred (substitution i g0 g1)}.
Proof. intros. destruct H,H0. constructor.
elim : g0 g1 i H H0;intros;rewrite /=; simpl in *;try done. 
- rifliad. cc.
- cc.  
- rifliad. cc. cc. apply H;cc.
-  cc; apply H; cc. 
- have : (project_pred (GBranch a l)) by cc. rewrite /= !big_map. intros. rewrite !all_map. apply/andP.  split. apply/allP=> x' Hin. 
  simpl. rewrite /projmap. apply/allP=>p. rewrite !inE. intros. apply/ueqeP.
  erewrite nth_map. rewrite !project_subst. 
Admitted. 
(*apply/eqP/fmapP=>k. rewrite !mapf_if. case_if. f_equal.
  move : Hin. move/nthP=>HH'. specialize HH' with GEnd. destruct HH'. rewrite -H4. erewrite nth_map. 
  rewrite !project_subst. f_equal. apply :  project_predP_aux. cc. 
  move : H2. rewrite !inE. move/orP=>[]. rewrite /fresh. destruct ( atom_fresh_for_list ([fset ptcp_from a; ptcp_to a] `|` \bigcup_(j <- l) substitution i j g1)) eqn:Heqn. 
rewrite Heqn. move/eqP=>->. clear Heqn.
  move : n. move/negP. rewrite !inE. move/andP=>[]. 
done. move/andP=>[].  done. done. cc. cc. cc. done.  apply/allP=>k Hin.  simpl. apply H.  done. cc. cc. 
Qed.*)



Instance step_action : forall g l g', {goal step g l g'} -> {goal lpreds [::apred;spred] g} -> {goal apred g'}.  
Proof.
move => g l g' [] H [] H0. constructor. elim : H H0; rewrite /=;split_and;cc.
apply H0. cc.
apply H0. cc.
Qed.

Instance step_size : forall g l g',{goal step g l g'} -> {goal lpreds [::apred;spred] g} -> {goal spred g'}.  
Proof.
move => g l g' [] H [] H0. constructor.  elim : H H0; rewrite /=;intros;split_and;cc.
apply H0. cc. rewrite -H.  cc. apply H0. cc. 
Qed.


Instance linear_sgmsg : forall a u g0, {hint Linear (GMsg a u g0)} -> {goal Linear g0}.
Proof. 
move => a u g0. apply chint_imp. rewrite /Linear /=.  intros. move : (H (a::aa_p) a0 aa a1). rewrite cat_cons /=. 
  destruct ( aa_p ++ a0 :: rcons aa a1) eqn:Heqn. case : aa_p H0 Heqn.  done. done.
  intros. have : Tr ((a::aa_p ++ (a0::aa) ++ [::a1])) (GMsg a u g0). auto.  move/H2 => H3.  move : (H3 H1). 
  move => [] mi [] mo. intros. auto. 
Qed.

Instance linear_branch_aux : forall a gs, {hint Linear (GBranch a gs)} -> {goal Forall Linear gs}.  
Proof.
move => a gs. apply chint_imp. intros. apply/List.Forall_forall. intros. rewrite /Linear. intros. unfold Linear in H. have : Tr (a::aa_p ++ a0::aa ++ ([::a1])) (GBranch a gs). move : H0.  move/In_in. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth. rewrite -H3 in H1. apply : TRBranch. eauto. apply : H1. 
intros. apply : H. rewrite -cat_cons in x0. apply : x0. done. 
Qed.

Instance linear_branch : forall a gs n, {hint Linear (GBranch a gs)} -> {goal n < size gs} -> {goal Linear (nth GEnd gs n)}.
Proof. intros. destruct H,H0.  apply Build_CHint in H. apply linear_branch_aux in H. destruct H. move : H. move/Forall_forall. intros. constructor. eauto. Qed.


Instance linear_unf : forall g n, {hint Linear (GRec n g)} -> {goal Linear g[g GRec n g//n]}.
Proof. move => g n. apply chint_imp.
intros.  unfold Linear in *. intros. apply : H. constructor. eauto. done. 
Qed.

Lemma step_tr : forall g vn g', step g vn g' -> lpreds [::spred] g ->  exists s, Tr (s ++ [::vn.1]) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) s.
Proof.
move => g vn g'. elim.
- intros. exists nil. rewrite /=. auto.
- intros. exists nil. rewrite /=. split;auto.  apply TRBranch with (n:=n)(d:=GEnd). done. done.
- intros.  simpl in H2. destruct H0. cc. destruct H0. exists (a::x). rewrite /=. auto. 
- intros. move : H1. move/Forall_forall=>Hall. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') 0).
  rewrite nth_zip in Hall.  simpl in Hall. have : exists s : seq action, Tr (s ++ [:: l.1]) (nth GEnd gs 0) /\ Forall (fun a : action => ptcp_to a \notin l.1) s. apply Hall.  rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H. 
  have :  size gs' - (size gs' - size gs') = size gs' by lia. move=>->. simpl in H3. rewrite -H. cc. lia. cc. intros. destruct x,H1. exists (a::x). simpl. split;auto.  apply TRBranch with (n:=0)(d:=GEnd).  cc. done. done. 
- intros. destruct H0.  cc. destruct H0. exists x. auto. 
Qed.

(*Linear should be included in *)

Definition linear (g : gType) := true. 
Lemma linearP : forall g, reflect (Linear g)  (linear g) . 
Admitted.




(*Lemma In_exists : forall (A : Type) (a : A) l, In a l -> exists (l0 l1 : seq A), l = l0 ++ (a::l).*)
Lemma ch_diff : forall g a0 aa a1, lpreds [::linear] g -> Tr (a0::(aa++[::a1])) g  -> Forall ( fun a => (ptcp_to a) \notin a1) (a0::aa) ->  Forall (fun a => action_ch a != action_ch a1) (a0::aa).
Proof.
intros. apply/List.Forall_forall. intros. 
destruct (eqVneq (action_ch x) (action_ch a1)); last done. inversion H1. subst.
exfalso. simpl in H2. destruct H2. 
- subst. apply : no_indep. apply : H5.  apply H6. nth_lpreds 0 H. move/linearP/Linear_1=>HH.  apply : HH. 
  rewrite -[_::_]cat0s in H0. apply : H0. rewrite /same_ch. apply/eqP. done.
- apply List.in_split in H2.  destruct H2,H2. rewrite H2 in H0. nth_lpreds 0 H. move/linearP=>HH.  rewrite /Linear in HH.
  specialize HH with (a0::x0) x x1 a1. 
have : (a0 :: (x0 ++ (x :: x1)%SEQ)%list ++ [:: a1]) = ((a0 :: x0) ++ x :: x1 ++ [:: a1]).
  rewrite /=. f_equal. rewrite -catA. f_equal.


  intros. move : H0.  rewrite x2. move/HH=>H3. 
  have : same_ch x a1. by rewrite /same_ch e. move/H3. case. intros. move : H1.  
  rewrite H2. intros. inversion H1. apply List.Forall_app in H8. destruct H8. inversion H9. apply : no_indep. 
  apply H12.  apply H13.  done.
Qed.

Lemma distinct_ch : forall g vn g', step g vn g' -> lpreds [::linear;size_pred] g ->  exists s, Tr (s ++ [::vn.1]) g /\  Forall (fun a =>  (action_ch a) != (action_ch vn.1)) s.
Proof. intros. edestruct (step_tr). eauto. cc. destruct H1. exists x. split;auto. inversion H2. done. apply : ch_diff. cc. 
subst. eauto.  auto. 
Qed.

Lemma distinct_ch_msg : forall a u g vn g', step (GMsg a u g) vn g' -> ptcp_to a \notin vn.1 ->lpreds [::linear;size_pred] (GMsg a u g) -> (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto. cc.  destruct H2. move : H3. move/Forall_forall=>HH.  destruct x. simpl in H2. inversion H2. subst. rewrite !inE in H0. split_and. simpl in H2.  inversion H2. subst. apply HH. rewrite !inE. done.
Qed.

Lemma distinct_ch_branch : forall a gs vn g', step (GBranch a gs) vn g' -> ptcp_to a \notin vn.1 ->lpreds [::linear;size_pred] (GBranch a gs) -> (action_ch a) != (action_ch vn.1).
Proof. intros.  edestruct distinct_ch. eauto. cc.  destruct H2. move : H3. move/Forall_forall=>HH.  destruct x. simpl in H2. inversion H2. subst. rewrite !inE in H0. split_and. simpl in H2.  inversion H2. subst. apply HH. rewrite !inE. done.
Qed.


Lemma step_test : forall g l g', step g l g' -> lpreds (bound::linear::rec_pred) g ->  Estep (project g (ptcp_from l.1)) (Sd,action_ch l.1,l.2) (project g' (ptcp_from l.1)).
Proof. move => g l g'. elim.
- intros. rewrite /= eqxx. auto.  
- intros. rewrite /= eqxx. erewrite <- (@nth_map _ _ _ EEnd (fun g => project g (ptcp_from a))).    apply estep_branch. by   rewrite size_map.  done. 
- intros. move : H1. move/[dup]. intros. rewrite !inE in H1.  rewrite /=. 
  split_and. rewrite [_ == ptcp_to a]eq_sym. rewrite (negbTE H4).
  rifliad.
 * constructor. auto. apply H0.  cc. apply/eqP. rewrite neg_sym.  apply : distinct_ch_msg.  eauto. eauto. cc. 
 * apply : H0. cc. 
- intros. rewrite /=. move : H2. move/[dup]. move=>H2 Hdup. rewrite !inE in H2. split_and. rewrite eq_sym. rifliad.
 * constructor. auto. rewrite !size_map. done. apply/Forall_forall. move => x. 
   move/nthP=>HH. specialize HH with (EEnd,EEnd). destruct HH. 
 move : H6.  rewrite size_zip !size_map  H minnE nat_fact. intros. 
clear H4. rewrite nth_zip in H7. rewrite -H7 /=. 
   repeat erewrite (@nth_map _ GEnd _ EEnd (fun g => project g (ptcp_from l0.1))).  
   move : H1. move/Forall_forall=>Hall;intros. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') x0).
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. done. done. all: cc. 
   rewrite !size_map. done.
 * apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. eauto. eauto. cc. constructor.  auto. 
   by rewrite !size_map.
 * apply/(@forallP _ _ (EEnd,EEnd)).  intros. move : H1. move/Forall_forall=>HH0. specialize HH0 with (nth (GEnd,GEnd) (zip gs gs') x0).
   move : H7.   rewrite size_zip minnE !size_map H nat_fact=>H7. 

   rewrite nth_zip /= in HH0. rewrite nth_zip /=.  
   rewrite -!nth_project in HH0. apply : HH0. rewrite -nth_zip. apply/mem_nth.  rewrite size_zip minnE H nat_fact. done.
   done. cc.  by rewrite !size_map. done. apply/eqP. rewrite neg_sym. apply : distinct_ch_branch. 
   eauto. eauto. cc.
 * rewrite !match_n.
   move : H1. move/Forall_forall=>Hall. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') 0). 
   rewrite nth_zip in Hall. simpl in Hall. apply Hall. rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H.
   have : size gs' - (size gs' - size gs') = size gs' by lia. move=>->. simpl in H4. rewrite -H. cc. all : cc. 
- intros. (*have : lpreds rec_pred (GRec n g0) by cc. clear H3. move=> H3.*) rewrite /=. rifliad. 
 * rewrite !project_subst in H0.  rewrite (eqP H2) /= eqxx H2 in H0. apply H0.  cc. cc. 
 * econstructor. pfold.  econstructor. left. eauto. rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0.   apply H0. cc. cc. 
- rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0. rewrite subst_nop in H0. apply H0. cc. by rewrite H3. cc. 
Grab Existential Variables. eauto.
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
 * rewrite !project_subst in H0.  rewrite (eqP H2) /= eqxx H2 in H0. apply H0.  cc. cc. 
 * econstructor. pfold.  econstructor. left. eauto. rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0.   apply H0. cc. cc. 
- rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0. rewrite subst_nop in H0. apply H0. cc. by rewrite H3. cc. 
Grab Existential Variables. eauto.
Qed.


Lemma step_test3 : forall g l g', step g l g' -> lpreds (bound::linear::rec_pred) g ->  forall p, p \notin l.1 -> (project g p) =f= (project g' p).
Proof. 
move => g l g'. elim;intros.
- simpl in H0.  rewrite /=. move : H0. rewrite !inE. split_and.  rewrite (negbTE H1) (negbTE H2).
- simpl in H1.  rewrite /=. move : H1. auto.  
- rewrite /=. intros. simpl in H1.  move : H1. rewrite !inE. split_and. rewrite (negbTE H2) (negbTE H3) match_n.
  apply : project_predP_aux. cc. rewrite !inE. split_and. cc. 
- simpl.  rifliad. pfold. constructor. left. apply H0. cc. done. pfold. constructor. left. apply H0. cc. done. 
  apply H0. cc. done.
- rewrite /=. rifliad. pfold. constructor. by rewrite !size_map.
  have : (all (lpreds (bound::linear::rec_pred)) gs). cc. intros. clear H3. elim : gs gs' H H0 H1 x. case. simpl. auto. done. move => a0 l1 IH. case. done. intros. simpl. constructor.  left. simpl. simpl in H1. inversion H1. subst. 
  simpl in H7.  apply H7. move : x.  simpl. split_and. done. simpl in H1.  apply IH;auto. simpl in H0. inversion H0. done. inversion H1. done. simpl in x. split_and. 

  pfold. constructor. by rewrite !size_map.
  have : (all (lpreds (bound::linear::rec_pred)) gs). cc. intros. clear H3. elim : gs gs' H H0 H1 x. case. simpl. auto. done. move => a0 l1 IH. case. done. intros. simpl. constructor. simpl in H1. inversion H1. subst. 
  simpl in H8.  left. simpl. apply H8. move : x.  simpl. split_and. done. simpl in H1.  apply IH;auto. simpl in H0. inversion H0. done. inversion H1. done. simpl in x. split_and. 

  rewrite !match_n. move : H1. move/Forall_forall=>Hfor. specialize Hfor with (nth (GEnd,GEnd) (zip gs gs') 0) p. rewrite nth_zip /= in Hfor. apply Hfor.  rewrite -nth_zip. apply/mem_nth.  rewrite size_zip minnE H nat_fact -H. cc. done. cc. done. done. 
- simpl.  rifliad. 
- intros.  apply : ueqe_trans.  2 : { apply : H0. cc. done. } rewrite project_subst. rewrite (eqP H3) /= eqxx H3. auto. cc.
 * apply : ueqe_trans.  2 : { apply : H0. cc. done. } pfold. rewrite project_subst. constructor. left. rewrite /= H3 H4.  auto. cc. 
   apply : ueqe_trans. 2 : {  apply : H0. cc. done. } rewrite project_subst /=. rewrite H3 H4. rewrite subst_e_nop. auto.
   apply/negP. by rewrite H4. cc.
Qed.


Lemma harmony1 : forall g l g' S, lpreds (bound::linear::rec_pred) g -> step g l g' -> l.1 `<=` S ->  EnvStep (projmap S g) l (projmap S g').
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

