From mathcomp Require Import all_ssreflect zify.
From mathcomp Require Import finmap.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Dep Require Import NewSyntax Bisimulation.

Let inE := NewSyntax.inE.



Fixpoint project g p := 
match g with 
| GEnd => EEnd
| GMsg a u g0 => if p == (ptcp_from a) then EMsg Sd (action_ch a) u (project g0 p) 
                               else if p == (ptcp_to a) then EMsg Rd (action_ch a) u (project g0 p) else project g0 p
| GBranch a gs => if p == (ptcp_from a) then EBranch Sd (action_ch a) (map (fun g => project g p) gs)
                                else if p == (ptcp_to a) then EBranch Rd (action_ch a) (map (fun g => project g p) gs) else if gs is g'::gs' then project g' p else EEnd
| GRec g => if (project g p) == EVar 0 then EEnd 
            else   ERec( project g p)
| GVar n => EVar n
end.

Lemma match_n : forall (gs : seq gType) k,  match gs with
  | [::] => EEnd
  | g'0 :: _ => project g'0 k end = project (nth GEnd gs 0) k.
Proof.
elim. done. intros. rewrite /=. done.
Qed.

Lemma big_exists : forall (A : eqType) (B : choiceType) (l : seq A) (f0 : A -> {fset B}) p, p \in \bigcup_(j <- l) (f0 j) = has (fun x => p \in f0 x) l. 
Proof. 
move => A B. elim. move => f0 p. rewrite big_nil. done. intros. simpl. rewrite big_cons !inE. destruct ( (p \in f0 a) ) eqn:Heqn;rewrite /=. 
done.
apply H.
Qed.


Lemma project_ren : forall g p sigma, project (g ⟨ sigma ⟩) p = (project g p) ⟨ sigma ⟩.
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if.
 * rewrite (eqP H0) //=.
 * case_if.
  ** exfalso. move : H1 H0.  
     move/eqP. destruct (project g p);asimpl;rewrite /=. case. destruct n. asimpl. done. asimpl.
done. all : try done. 
simpl.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
rewrite !match_n. induction l. done. simpl. apply H. auto. 
Qed.


Lemma project_subst : forall g p sigma, project (g[g sigma]) p = (project g p) [ sigma >> (fun g => project g p)].
Proof.
elim;intros.
- simpl. done.
- done.
- simpl. asimpl. rewrite H. symmetry. case_if.
 * rewrite (eqP H0) //=.
 * case_if.
  ** exfalso. move : H1 H0.  
     move/eqP. destruct (project g p);asimpl;rewrite /=. destruct n. asimpl. done. asimpl. simpl. 
     rewrite project_ren. all : try done. 
     destruct  (project (sigma n) p);simpl;asimpl.
     destruct n0. done. done. all : try done. 
     simpl. f_equal. asimpl. simpl. f_equal.
     fext. intros. destruct x. asimpl. done.
     asimpl. simpl. rewrite project_ren. done.
simpl.
rifliad;asimpl;try done. f_equal. auto.  f_equal. auto. auto.
simpl. rifliad;asimpl;try done. f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
 f_equal. rewrite -!map_comp. apply/eq_in_map=>l'. intros. simpl.
apply H. done. 
rewrite !match_n. induction l. done. simpl. apply H. auto. 
Qed.


Definition fset_ptcp := {fset ptcp}.
Definition env := {fmap ptcp -> endpoint}.
Definition projmap  (S : fset_ptcp) (g : gType)  : env := [fmap p : S => project g (val p)].


Definition ptcp_le (p0 p1 : ptcp) := let: Ptcp n0 := p0 in let: Ptcp n1 := p1 in n0 <= n1.

  Lemma nat_list_max : forall (xs : list ptcp),
    { n : ptcp | forall x, x \in xs -> ptcp_le x  n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists (Ptcp 0). inversion 1.
    (* case: cons x xs *) destruct x,y.
    exists (Ptcp (n + n0)%nat). intros z J. move : J. rewrite inE. move/orP=>[]. move/eqP=>->. rewrite /=. lia. move/H. rewrite /ptcp_le. destruct z.  lia. 
   Qed.

 Lemma atom_fresh_for_list :
    forall (xs : list ptcp), { n : ptcp | ~ n \in xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H]. destruct x. exists (Ptcp (n.+1)).
    intros J. rewrite /ptcp_le in H. apply H in J. lia. 
  Qed. 
Definition fresh (S : fset_ptcp) :=
    match atom_fresh_for_list S with
      (exist x _ ) => x
    end.


Fixpoint project_pred  (g : gType):=  
match g with 
| GMsg a u g0 => project_pred g0 
| GBranch a gs => let S := ptcps g in 
                 all (fun (g' : gType)  => 
                         all (fun p => ebisim_dec (project (nth GEnd gs 0) p) (project g' p)) 
                         (fresh S |` (S `\` a )))
                      gs 
                 && (all project_pred gs)
| GRec g0 => project_pred g0
| _ => true 
end.





(*Lemma endpoint_rename : forall e,  endpoint_fv (ren_endpoint predn e) = predn @` endpoint_fv e.
Proof. 
elim;rewrite /=;intros. rewrite Imfset.imfsetE /=. fsetTac. rewrite seq_fsetE.
apply bool_iff. split. move/eqP=>->. rewrite map_f //=. rewrite !inE //=. 
move/mapP=>[]. intros. rewrite !inE in p. rewrite -(eqP p) -q //= eqxx //=.
rewrite predn_fset0 //=.
f_equal.*)

(*Lemma fv_shiftdown : forall e i, i \notin (endpoint_fv i e)  -> endpoint_fv i (shiftdown e) = endpoint_fv i.+1 e.
Proof. 
elim;rewrite /=;try done;intros.
move : H. rifliad;rewrite !inE;intros. all : try fsetTac. 
rewrite -H //=. asimpl.  rewrite /shiftdown.
 asimpl. f_equal. clear H0. clear H. rewrite /scons.
fext.  intros. 
Admitted.
*)

(*Lemma fv_predn : forall e, endpoint_fv e ⟨ predn ⟩ = [fset predn n | n in endpoint_fv e].
Proof. intros. fsetTac. destruct (k \in endpoint_fv e ⟨ predn ⟩) eqn:Heqn;rewrite Heqn /= bbrw.
apply/imfsetP.
elim : e k Heqn;intros.
- exists n. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.
- rewrite /= !inE //= in Heqn. 
- rewrite /= ?inE in Heqn.
  exists k. rewrite /=. move : Heqn. asimpl. move => HH.  
  have :  (k \in endpoint_fv e ⟨e predn ⟩). admit. move/H=>[]. move => x. simpl.
  intros. apply/imfsetP. exists x. simpl. rewrite !inE /=. split_and. 
  have : ( 0 .: predn >> succn ) = (0 .: id). fext. intros.  case. done. intros. simpl. destruct n. asimpl.  simpl. done.
asimpl_in Heqn. rewrite /= !inE //=. move : Heqn. rewrite /= !inE //=. lia.

 -
  elim;intros.
fsetTac. destruct (eqVneq k n.-1). rewrite bbrw.  
apply/imfsetP. exists n. simpl. rewrite !inE //=. done. 
rewrite bbrw.  move/imfsetP. move=>[] x. simpl. rewrite !inE. move/eqP=>->. lia. 
simpl. fsetTac. rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE //=.
fsetTac. asimpl.*)

(*Lemma subst_nop : forall e e' x, x \notin (fv e) -> subst_e x e e' = e. Proof. 
elim;rewrite /=;try done;intros. move : H. rewrite !inE.  rewrite neg_sym. move/negbTE=>->. done. 
move : H0. rewrite !inE. move/orP=>[]. by rewrite eq_sym=>->.  
intros. rifliad. rewrite H //=. 
f_equal. auto. f_equal. rewrite big_map in H0.  induction l. done. simpl. f_equal.  apply H.  rewrite !inE.  lia. simpl in H0. move : H0. 
rewrite big_cons. rewrite !inE. split_and. apply IHl. intros. apply H. rewrite !inE H1. lia. done. move : H0.  rewrite big_cons !inE. split_and. 
Qed.*)




(*Lemma fv_subst : forall  e e' n x, fv e' = fset0 -> n <> x -> (n \in (fv (subst_e x e e'))) = (n \in (fv e)).
Proof. elim;rewrite /=;try done;intros. rewrite !inE. rifliad. rewrite H !inE. have : n0 == n = false by lia. by move=>->. 
rewrite /= !inE. done. 
rifliad. rewrite /=. Check mem_map. Search (_ \in (map _ _)). Search _ (_ \in _ = _ \in _).  Search _ ((is_true _ -> is_true _) -> _ = _). rewrite !inE.  destruct (n0 != n)eqn:Heqn;rewrite /= //=.   rewrite Heqn //=.
apply H. done. done. rewrite Heqn //=. 
rewrite !big_map.  elim : l H. rewrite !big_nil. done. intros. rewrite !big_cons. rewrite !inE. rewrite H2 //=. 
destruct ( (n \in fv a)) eqn:Heqn; rewrite !Heqn //=. apply H. intros. apply H2. rewrite !inE H3. lia. done. done. 
Qed.*)

(*Lemma fv_nil_evar : forall e n, endpoint_fv 0 e = fset0 -> e <> EVar n. 
Proof.
elim;rewrite /=;try  done. intros. have : n \in [fset n]. by  rewrite !inE. move : H. have : n - 0 = n by lia. move=>->. move/fsetP=>->. done. 
Qed.

Lemma fset_nil : forall (A : choiceType) (n : A), [fset n] = fset0 -> False.
Proof. intros. move : H. move/fsetP=>HH. suff : n \in [fset n] = (n \in fset0). rewrite !inE eqxx //=. done. 
Qed.
*)
(*Lemma clean_up : forall e sigma, clean (endpoint_ren e S) [↑__endpoint sigma] = (clean e) [↑__endpoint sigma].*)

(*Lemma in_subst : forall e sigma, (endpoint_fv (e [e sigma])) = sigma @` (endpoint_fv e).*)


(*Lemma in_subst : forall v e n sigma, v \in (endpoint_fv e) ->  sigma v = EVar n ->  n \in (endpoint_fv (e [e sigma])). 
Proof. 
move => v e. elim : e v;asimpl;intros. rewrite !inE in H. rewrite -(eqP H) H0 //= !inE //=. 
rewrite !inE //= in H.
rewrite /endpoint_fv -/endpoint_fv. rewrite seq_fsetE. Search _ (_ \in pmap _ _). rewrite mem_pmap. apply/mapP.  exists v. 
move : H0. rewrite /endpoint_fv -/endpoint_fv.  rewrite seq_fsetE mem_pmap. move/mapP=>[]. intros. apply : H. eauto. 
destruct x. done.  simpl. asimpl. simpl in q. done. simpl. substify. asimpl.

move : H0. simpl. rewrite mem_map.
simpl. rewrite fsetE.*)

(*

asimpl. simpl. symmetry. case_if. rewrite -(eqP H2). 
  move : H1. destruct (clean e);rewrite /=;asimpl. destruct n.  done. simpl. asimpl. destruct (sigma n);rewrite /=;asimpl. 
  destruct n0. all : try done. rifliad. substify. move/eqP. rewrite /shiftdown. asimpl. move : H1. substify. asimpl. rewrite H. 
  

have :  subst_endpoint (scons (var 0) (sigma >> (⟨ ↑ ⟩ >> clean)))  == var 0 = false.

case_if. 
  simpl. case_if. move : H2. 
asimpl. rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.

Lemma clean_subst : forall (e0 : endpoint)  e' x, endpoint_fv 0 e' = fset0 -> clean (e0[s e'//x]) = (clean e0)[s clean e'//x].
Proof.
elim;intros. 
- rs. rifliad.
- rs. done.
- rs. case_if.  
 * rs. rewrite (eqP H1) /=. rifliad. rs. by rewrite /= eqxx. rewrite subst_nop //=. rewrite fv_clean. lia. 
 * rs. rewrite /= H //=.  rewrite fv_subst //=. symmetry. case_if.
  ** rs. rewrite (eqP H2) /=. rs. rewrite H1 eqxx. done.
  ** case_if.
   *** rs. rewrite /= H1. rifliad. exfalso. move : H4.  destruct (clean e);rewrite /=;rs. rifliad. move/eqP. apply : fv_nil_evar. 
       rewrite fv_clean //=. by rewrite H2. done. done. done. rifliad. 

   *** rs. rifliad. exfalso. move : H5. rewrite !inE H3. have : n != x by lia. move=>->. done. rewrite !inE H3.
       have : n != x by lia. move=>-> /=. rifliad. 
       destruct (clean e);rewrite /=;rs.  rifliad. rewrite (eqP H5) in H4. rs_in H4. rewrite eqxx in H4. rewrite -fv_clean in H0.  rewrite (eqP H4) in H0. rs_in H0. by apply fset_nil in H0. rs_in H4. rewrite H5 in H4. lia. done.
      all : try  by move : (eqP H4).   rs_in H4. rifliad. rs. f_equal. auto.  rs. f_equal. 
- rewrite -!map_comp. apply/eq_in_map. move => ll Hin /=. rewrite H //=.
Qed.*)

(*Lemma rproject_subst : forall g g0 p i,  rproject (g[s g0//i]) p = (rproject g p)[s (rproject g0 p)//i].
Proof. elim;rewrite /=;try done;intros;rs. rifliad. rifliad. rewrite /=.  rewrite H. done.  
rifliad. simpl. rs. f_equal. done. simpl. rs. f_equal. done. 
rifliad. simpl. rs. f_equal. 
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. 
simpl. rs.  f_equal.
rewrite -!map_comp. apply/eq_in_map. move=>ll Hin. simpl. apply H.  done. destruct l. done. simpl. apply H. rewrite !inE. done. 
Qed.*)

(*
Lemma fv_rename : forall e f, endpoint_fv e ⟨ f ⟩ = [fset f n | n in (endpoint_fv e)].
Proof.
elim;rewrite /=;intros. fsetTac. destruct (eqVneq k (f n));rewrite bbrw.
apply/imfsetP. exists n. rewrite /= !inE eqxx. done. done.
move/imfsetP=>[] x.  rewrite /= !inE. move/eqP=>->. lia.
rewrite predn_fset0 //=. asimpl. Print up_ren. 
fsetTac. symmetry. destruct ( (k \in f @` [fset n.-1 | n in endpoint_fv e & n != 0])) eqn:Heqn;rewrite Heqn bbrw.
move : Heqn. move/imfsetP=>[] x /= H' H2. subst.  move : H'. move/imfsetP=>[] x0 /=. rewrite !inE /=.
split_and. subst.  rewrite H. 
simpl. apply/imfsetP. exists x0. rewrite /= !inE H1  andbC /=. rewrite H. 
apply/imfsetP. exists x0. simpl. done. destruct x0.  done. simpl. have : f = predn. admit. move=>->. destruct x0. done. asimpl. simpl. move : H'.rewrite !inE. split_and.  exists x0.  done. rewrite H2 q. destruct x0. done. 
 simpl.  asimpl. admit.
done. simpl. asimpl. 
simpl in q. subst.  simpl.
Lemma fv_clean : forall e, endpoint_fv (clean e) = endpoint_fv e. 
Proof. elim;try solve [rewrite /=;try done];intros. 
rewrite /=. rifliad;simpl. 
fsetTac. rewrite (eqP H0) /= in H. rewrite -H.   rewrite bbrw. move/imfsetP=>[] x. simpl. rewrite !inE. split_and. lia.
rewrite H. done. fsetTac. 
rewrite H. fsetTac.

rewrite (eqP H0) in H. simpl. simpl in H. rewrite -H. simpl in H.
fsetTac. apply/negP/negP. move=>_. move/imfsetP=>[]. move => x. simpl. rewrite !inE. split_and. lia. done. 
rewrite /shiftdown.  *)







(*Lemma inj_rem : forall e0 e1 f f', injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 ⟨e f' ⟩ = e1 ⟨e f' ⟩.
Proof. 
elim. intros. destruct e1;try done.  f_equal. move : H0. asimpl. case. move/H. by move=>->. 
- case;try done.
- intros. asimpl.  destruct e1;try done. f_equal. move : H1.  asimpl. intros. f_equal. 
  apply : H. have : injective (0 .: f >> succn ).
  intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H0. done. move => HH. apply : HH. 

(*intro. intros. destruct x1;destruct x2. done. move : H.  asimpl.
done.  move : H. asimpl. done. f_equal. move : H. asimpl. case. move/H1. done. *)
  move : H1.  asimpl. case. intros. eauto.
- intros. destruct e1;try done.
 move : H1.  asimpl. case. intros.  subst. f_equal. eauto. 
- intros. move : H1.  asimpl. destruct e1;try done. asimpl. case. intros. subst. f_equal.
  move : H3. elim : l l0 H;simpl. destruct l0. done. done. destruct l0. done. 
  simpl. intros. f_equal. apply : H1. auto. eauto. inversion H3. done.  apply H. 
  intros. apply : H1. eauto. eauto. eauto.  inversion H3. eauto. 
Qed.


Lemma inj_rem2 : forall e0 e1 f , injective f  -> e0 ⟨e f⟩ = e1 ⟨e f⟩ -> e0 = e1.
Proof. intros. have : e0 = e0 ⟨id⟩.  asimpl. done. move=>->. 
have : e1 = e1 ⟨id⟩. asimpl. done. move=>->. apply/inj_rem. eauto. eauto.
Qed.*)





(*
Lemma inj_rem4 : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e ⟨e f⟩  = e ⟨e f'⟩ .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE //=. done.
asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.

Lemma inj_rem5 : forall e  f f' v , 
 e ⟨e f⟩  = e ⟨e f'⟩ ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have : (f v).+1 <> (f' v).+1. move => H'. inversion H'. apply H1. 
done.  move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.


Lemma inj_rem4' : forall e  f f' , 
(forall v, v \in endpoint_fv e -> f v = f' v) -> e [e f]  = e [e f'] .
Proof.  
elim;intros.
- asimpl. rewrite H.  done. rewrite /= !inE. done.
done. asimpl. f_equal.  apply H.  intros. destruct v. done. asimpl. rewrite H0. done. 
simpl. apply/imfsetP. exists v.+1. simpl. rewrite !inE. split_and. done. asimpl. f_equal. apply H. auto. 
asimpl. f_equal. apply/eq_in_map. move => g. intros. apply H. done. intros.  apply H0.
simpl. rewrite big_map. rewrite big_exists. apply/hasP. exists g. done. done.
Qed.

Lemma inj_rem5' : forall e  f f' v , 
 e [e f]  = e [e f'] ->  f v <> f' v -> v \notin endpoint_fv e.
Proof.  
elim;intros;rewrite /= ?inE;try done. move : H. asimpl. case. intros. destruct (eqVneq v n). subst. done. done. 
move : H0. asimpl. case. move/H=>HH. apply/negP. move/imfsetP=>[] x /=. rewrite !inE. split_and. 
specialize HH with v.+1.  move : HH. asimpl. move => HH. have :  (f v) ⟨e ↑ ⟩ <> (f' v) ⟨e ↑ ⟩.  
 move => H'. apply inj_rem2 in H'. apply H1. done. intro. rewrite /shift.  intros. inversion H3. done. 
move/HH. subst. simpl. destruct x. done. simpl. simpl in *. rewrite H0 //=. 
apply: H. move : H0. asimpl. case. eauto. eauto.
rewrite big_map big_exists. move : H0. asimpl. case. move/eq_in_map=>HH.
apply/negP.  move/hasP=>[] x. intros. apply/negP. apply  H with (f:=f)(f':=f'). all : eauto. 
Qed.

*)



(*Fixpoint same_vars (e : endpoint ) :=
match e with 
| EBranch d c l => all (fun e' => endpoint_fv (nth EEnd l 0) == endpoint_fv e') l && (all same_vars l)
| EMsg _ _ _ e0 => same_vars e0
| ERec e0 => same_vars e0
| _ => true 
end.

Fixpoint same_varsg (e : gType ) :=
match e with 
| GBranch c l => all (fun e' => gType_fv (nth GEnd l 0) == gType_fv e') l && (all same_varsg l)
| GMsg _ _ e0 => same_varsg e0
| GRec e0 => same_varsg e0
| _ => true 
end.*)




(*Lemma in_foldr : forall l n,  n \in foldr (fun g' : gType => cat (fv_g g')) nil l ->  exists g, g \in l /\ n \in (fv_g g).
Proof. elim;try done;move => l n H n'.
rewrite /= mem_cat. move/orP=>[]. intros. exists l. rewrite !inE /= a. auto.
move/H. move=>[] x [].  intros. exists x. rewrite !inE a b. lia. Qed.*)

(*Lemma in_foldr2 : forall l n p g, g \in l -> n \in (fv (project  g p)) ->  n \in foldr (fun g' : gType => cat (fv (project g' p))) nil l.
Proof. elim;try done;intros. move : H0.
rewrite !inE. move/orP=>[]. move/eqP. intros. subst. simpl. rewrite mem_cat H1. done. intros.  simpl. rewrite mem_cat. apply/orP. right. apply : H. eauto. done. 
Qed.*)


(*
Lemma fv_project_in : forall g p n, lpreds rec_pred g ->  (n \in (fv_g g)) -> (n  \in (fv (project g p))).
Proof.
elim;rewrite //=;intros. move : H1. rewrite !inE.  split_and. apply (H p) in H3;last cc.
- rifliad. rewrite (eqP H1) in H3. simpl in H3. rewrite !inE in H3. lia. 
  simpl. Admitted. 
(*rewrite !inE.  split_and. 
- apply (H p) in H1;last cc. rifliad.
- rifliad. simpl. rewrite !big_map. 
  apply : big_cup_in.  intros. apply : H. done. cc. cc. apply/big_cup_in.  intros. apply : H4.  apply/big_cup_in. intros. apply : H4. rewrite big_map in H1. done. 
  rewrite /= !big_map.  apply : big_cup_in.  intros. apply : H. done. cc. eauto. rewrite big_map in H1. done. 
- rewrite match_n. apply H. cc. cc. move : H1. rewrite big_map foldr_exists. move/hasP=>[] x. intros. 
  intros.  move : p0. move/nthP=>Hnth. specialize Hnth with GEnd. destruct Hnth.

  apply : fv_rproject_in. 
  erewrite project_predP. apply : H. apply/mem_nth. apply : H1. cc. rewrite H4.  done. eauto.  cc.   all:cc. instantiate (1 := fresh a). rewrite /fresh. destruct (atom_fresh_for_list a). apply/negP.  move => HH. apply n0. destruct a. move : HH. rewrite !inE.  done. 
Qed.*)

Lemma fv_project_eq : forall g p n, lpreds rec_pred g ->  (n \in fv_g g) = (n \in fv (project g p)).
Proof. intros. destruct ( (n \in fv_g g)) eqn:Heqn. rewrite fv_project_in //=.
destruct ((n \in fv (project g p))) eqn:Heqn2. erewrite fv_rproject_in in Heqn. done. eauto. done. 
Qed.*)


