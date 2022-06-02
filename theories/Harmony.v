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

Definition map_subst (i : nat) (d : env) g := [fmap x : (domf d) => (try_fnd d (val x))[s (project g (val x))//i]]. 


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





Lemma projmap_subst : forall g0  g i S, lpreds [::bound] g -> projmap S (g0[s g//i]) = map_subst i (projmap S g0) g.
Proof.
intros. rewrite /projmap /map_subst. apply/fmapP=>k. rewrite !mapf_if. 
rewrite (@mapf_if _ _ _ (fun x =>  (try_fnd ([fmap p => project g0 (val p)]) (x))[s (project g (x))//i])) /=.
rifliad. f_equal. rewrite project_subst. rewrite /try_fnd. rewrite mapf_if H0. done. done. 
Qed.



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


Fixpoint same_vars (e : endpoint ) :=
match e with 
| EBranch d c l => all (fun e' => fv (nth EEnd l 0) == fv e') l && (all same_vars l)
| EMsg _ _ _ e0 => same_vars e0
| ERec _ e0 => same_vars e0
| _ => true 
end.

Fixpoint same_varsg (e : gType ) :=
match e with 
| GBranch c l => all (fun e' => fv (nth GEnd l 0) == fv e') l && (all same_varsg l)
| GMsg _ _ e0 => same_varsg e0
| GRec _ e0 => same_varsg e0
| _ => true 
end.


Lemma ueqe_fv : forall e0 e1, e0 =f= e1 -> fv e0 = fv e1. 
Proof. Admitted.


Lemma fv_eq : forall g p, lpreds rec_pred g  -> fv g = fv (project g p). Admitted.

Lemma ppred_same_vars : forall g p, lpreds rec_pred g ->  same_vars (project g p).
Proof. 
elim;rewrite//=;rs;intros. rifliad;simpl;auto. all: try apply H; cc. rifliad;simpl;auto. all : try apply H; cc.
rifliad. simpl. split_and. apply/allP=>e'. intros. move : H2. move/mapP=>[]. intros. subst.  erewrite nth_map.  
nth_lpreds 2 H0. simpl. move => HH. apply/eqP/ueqe_fv/ueqeP. split_and. cc. 
rewrite all_map. apply/allP. intro.  intros. simpl. apply H. done. cc. simpl. 
split_and. 
apply/allP=>e'. intros. move : H3. move/mapP=>[]. intros. subst.  erewrite nth_map.  
nth_lpreds 2 H0. simpl. move => HH. apply/eqP/ueqe_fv/ueqeP. split_and. cc. 
rewrite all_map. apply/allP. intro.  intros. simpl. apply H. done. cc. 
rewrite match_n. apply H. cc. cc. 
Grab Existential Variables. all: repeat constructor.
Qed.

Lemma ppred_same_varsg : forall g, lpreds rec_pred g -> same_varsg g.
Proof.  
elim;rewrite /=;rs;intros;try done. apply H. cc. apply H.  cc.
split_and. apply/allP=>e' Hin. erewrite !fv_eq. apply/eqP. apply/ueqe_fv. apply/ueqeP. nth_lpreds 2 H0. simpl. split_and.
cc. cc. apply/allP=>x. intros. apply H. done. cc. 
Grab Existential Variables. all : repeat constructor.
Qed.


Lemma subst_distr : forall e e' e2 n n0, lpreds [::bound] e' ->  n<> n0 ->  fv e2 `<=` fv e ->  same_vars e -> e[s e' // n][s e2[s e' // n] // n0] = e[s e2//n0][s e' // n].  
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
Qed.

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

Lemma big_ptcp_subst_if : forall l g1 i, (\bigcup_(j <- l) ptcps (j)[s g1 // i]) = 
                                                      if i \in \bigcup_(j <- l) fv j
                                                          then \bigcup_(j <- l)  ptcps j `|` (ptcps g1) 
                                                          else \bigcup_(j <- l) ptcps j.
Proof.
elim;intros;rewrite /= ?big_nil ?big_cons !inE. done. rewrite H !ptcps_subst. case_if; rewrite H0 /=.  rifliad. fsetPtac. 
fsetPtac. case_if. fsetPtac. fsetPtac.
Qed.

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

Lemma traverse_project_pred_unf : forall g0 g1 i, ppred g0 && ppred g1 -> ppred g0[s g1// i].
Proof. 
intros. destruct (i \notin fv g0) eqn:Heqn. rewrite subst_nop //=. split_and. 
elim : g0 g1 i Heqn H;intros;rewrite /=. 
- move : Heqn. rewrite /= !inE. move/negbT. rewrite !inE. rewrite eq_sym.  rs. move=>->. done. done. 
- move : Heqn. rs.  rewrite /= !inE. move/orP/orP. rewrite !inE. split_and. have: n == i = false by lia. move=>->. 
  simpl. apply H. by rewrite H2. 
- split_and. 
- split_and. apply H. done. split_and.
- rewrite /= !big_map !all_map big_ptcp_subst_if. apply/andP.  split. rifliad. 
 * apply/allP=> x' Hin. simpl. apply/allP=>p. rewrite !inE. intros. split_and. 
 * rs. rs_in Heqn. split_and.  rewrite /= big_map H1 in Heqn. done. 
 * apply/allP=>g'. intros. simpl. apply H. done. suff : i \in fv g'. by  move=>->. 
   have : i \in fv (GBranch a l). lia. split_and. move : (ppred_same_varsg H2). simpl. split_and.  rs_in x. rewrite /= big_map big_exists in x. destruct (hasP x). rewrite -(eqP (allP H0 _ H5)) in H6. rewrite -(eqP (allP H0 _ H1)). done. split_and. simpl in H2. split_and. by apply (allP H4).
Qed.

(*Lemma traverse_project_pred_unf : forall g0 g1 i, lpreds rec_pred g0 -> lpreds ([::bound;project_pred]) g1 -> g1 `<=` g0 -> project_pred (substitution i g0 g1).
Proof. 
elim;intros;rewrite /=; simpl in *;try done. 
- rifliad. cc.
- rifliad. cc. simpl. apply H. cc. cc. done.
- apply H. cc. cc. admit.
- have : (project_pred (GBranch a l)) by cc. rewrite /= !big_map. intros. rewrite !all_map. apply/andP.  split. 
 * apply/allP=> x' Hin. simpl. apply/allP=>p. rewrite !inE. intros. apply/ueqeP.
   erewrite nth_map. rewrite !project_subst. apply ueqe_subst. apply ppred_same_vars.  cc. apply ppred_same_vars. cc. cc. 
   split_and. move : H3.  move/orP=>[]. move/eqP=>->. 
(*  have :  project (nth GEnd l 0) (fresh (a `|` \bigcup_(j <- l) (j)[s g1 // i])) =  project (nth GEnd l 0) (fresh (a `|` \bigcup_(j <- l) j)).*)
  erewrite project_tw0.  apply/ueqeP/(allP (allP H4 _ Hin)). rewrite !inE. apply/orP. left. 
  rewrite big_ptcp_subst_if. rifliad.

   have : (a `|` (\bigcup_(j <- l) j `|` g1)) = a`|`  \bigcup_(j <- l) j.
  apply/fsetP=>k. rewrite !inE. kb (k == ptcp_from a). kb (k ==ptcp_to a). move : (fsubset_in H2).  move=>Hf. kb (k \in ptcps g1). rewrite orbC /=. apply Hf in Heqn1. by  rewrite !inE Heqn Heqn0 /= big_map in Heqn1. by rewrite orbC /=. 
  move=>->. done.  cc.

  rewrite /npred. rewrite big_ptcp_subst_if. rifliad. Search _ fresh. rewrite /fresh. destruct (atom_fresh_for_list  (a `|` \bigcup_(j <- l) (j)[s g1 // i]) ) eqn:Heqn. rewrite Heqn.
  apply/negP=>HH. apply n. move : HH. rewrite !inE. intros. apply/orP. right. rewrite foldr_exists. apply/hasP. exists (nth GEnd l 0). cc.
  rewrite ptcp_subst HH. done. 

  rewrite /npred. rewrite /fresh. destruct (atom_fresh_for_list  (a `|` \bigcup_(j <- l) j)) eqn:Heqn. rewrite Heqn.
  apply/negP=>HH. apply n. move : HH. rewrite !inE. intros. apply/orP. right. rewrite foldr_exists. apply/hasP. exists (nth GEnd l 0). cc.
  done.
  move=>->. 

  have :  project x'  (fresh (a `|` \bigcup_(j <- l) (j)[s g1 // i])) =  project x' (fresh (a `|` \bigcup_(j <- l) j)). admit.
  move=>->.


  apply/ueqeP. apply/(allP (allP H4 _ Hin)) . by rewrite !inE. 
  split_and. rewrite (negbTE H7) (negbTE H8) /= in H6. move : H6. rewrite foldr_exists. move/hasP=>[]. intros.
  apply/ueqeP/(allP (allP H4 _ p0)). rewrite !inE. apply/orP. left. done. cc. cc. cc. right. split_and. eauto. auto. rewrite (negbTE H7) (negbTE H8) /=. 
  rewrite foldr_exists. apply/hasP. exists x. done. rewrite ptcp_subst in q. destruct (orP q). done. split_and.


  split_and. apply/ueqeP. apply/(allP (allP H3 _ Hin)) . rewrite !inE H6 H7 /=. destruct (orP H5). destruct (orP H2). rewrite H8. apply/orP.  right. done. 
  rewrite H8. apply/orP. right. apply/orP.   left. by rewrite orbC.   rewrite H2. 
lia.

move : H2. rewrite !inE. move/orP=>[]. move/eqP=>->. move/orP=>[]. rewrite eqxx. . move=>Hall. 

  apply project_tw0. cc. 
  rewrite /npred. rewrite /fresh. destruct (atom_fresh_for_list  (a `|` \bigcup_(j <- l) (j)[s g1 // i]) ) eqn:Heqn. rewrite Heqn.
  apply/negP=>HH. apply n. move : HH. rewrite !inE. intros. apply/orP. right. rewrite foldr_exists. apply/hasP. exists (nth GEnd l 0). cc.
  apply ptcp_in_subst. done. 

  rewrite /npred. rewrite /fresh. destruct (atom_fresh_for_list  (a `|` \bigcup_(j <- l) j)) eqn:Heqn. rewrite Heqn.
  apply/negP=>HH. apply n. move : HH. rewrite !inE. intros. apply/orP. right. rewrite foldr_exists. apply/hasP. exists (nth GEnd l 0). cc.
  done.
  move=>->. 

cc. nth_lpreds n H*)









Definition linear (g : gType) := true. 
Lemma linearP : forall g, reflect (Linear g)  (linear g) . 
Admitted.


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

Lemma step_tr : forall g vn g', step g vn g' -> size_pred g ->  exists s, Tr (s ++ [::vn.1]) g /\ Forall (fun a => (ptcp_to a) \notin vn.1) s.
Proof.
move => g vn g'. elim.
- intros. exists nil. rewrite /=. auto.
- intros. exists nil. rewrite /=. split;auto.  apply TRBranch with (n:=n)(d:=GEnd). done. done.
- intros.  simpl in H2. destruct H0. done. destruct H0. exists (a::x). rewrite /=. auto. 
- intros. move : H1. move/Forall_forall=>Hall. specialize Hall with (nth (GEnd,GEnd) (zip gs gs') 0).
  rewrite nth_zip in Hall.  simpl in Hall. have : exists s : seq action, Tr (s ++ [:: l.1]) (nth GEnd gs 0) /\ Forall (fun a : action => ptcp_to a \notin l.1) s. apply Hall.  rewrite -nth_zip. apply/mem_nth. rewrite size_zip minnE H. 
  have :  size gs' - (size gs' - size gs') = size gs' by lia. move=>->. simpl in H3. rewrite -H. split_and. done.  simpl in H3. split_and. apply (allP H4). apply/mem_nth. done.  intros. destruct x,H1. exists (a::x). simpl. split;auto.  apply TRBranch with (n:=0)(d:=GEnd).  simpl in H3. split_and. done. done. 
- intros. destruct H0.  apply size_pred_subst. done. done.  exists x. split.  destruct H0. constructor. done. destruct H0. done. 
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
- intros. rewrite /=. move : H2. move/[dup]. move=>H2 Hdup.  rewrite !inE in H2. split_and. rewrite eq_sym. rifliad.
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
 * rewrite !project_subst in H0.  rewrite (eqP H2) /= H2 in H0. rs_in H0. rewrite eqxx  in H0. apply H0.  cc. cc. apply  traverse_project_pred_unf. split_and. cc. cc. cc.
 * econstructor. pfold.  econstructor. left. eauto. rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0.   apply H0. cc. cc. apply traverse_project_pred_unf. split_and.  cc. cc. cc.
- rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0. rewrite !subst_nop in H0. apply : H0. cc. nth_lpreds 0 H1. rewrite /bound. move/eqP=><-. rs. apply/eqP. rewrite mem_fsetD1 //=. erewrite fv_eq. lia. by apply/negbT. erewrite fv_eq. apply/negbT. eauto. cc. 
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
 * rewrite !project_subst in H0.  rs_in H0. rewrite H2 (eqP H2) in H0.  rs_in H0. rewrite eqxx in H0. apply H0.  cc. 
 * apply traverse_project_pred_unf.  split_and. cc. cc. cc. econstructor. pfold.  econstructor. left. eauto. rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0.   apply H0. cc. apply traverse_project_pred_unf. split_and. cc. cc. cc.
- rewrite /= !project_subst /= in H0. rewrite H2 H3 in H0. rewrite !subst_nop in H0. apply H0. cc. 
 nth_lpreds 0 H1. rewrite /bound. move/eqP=><-. rs. apply/eqP. rewrite mem_fsetD1 //=. erewrite fv_eq. lia. by apply/negbT. erewrite fv_eq. apply/negbT. eauto. cc. 
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
- intros.  apply : ueqe_trans.  2 : { apply : H0. cc. apply traverse_project_pred_unf.  split_and. cc. cc. done. } rewrite project_subst. rs. rewrite H3  (eqP H3) /=. rs. rewrite eqxx. auto. cc.
 * apply : ueqe_trans.  2 : { apply : H0. cc. apply traverse_project_pred_unf. split_and. cc. cc. done. } pfold. rewrite project_subst. constructor. left. rewrite /= H3 H4.  auto. cc. 
   apply : ueqe_trans. 2 : {  apply : H0. cc. apply traverse_project_pred_unf. split_and. cc. cc. done. } rewrite project_subst /=. rewrite H3 H4. rewrite subst_nop. auto.
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

