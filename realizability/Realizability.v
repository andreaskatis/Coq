Definition admit {T: Type} : T.  Admitted.

(* --- Towards Realizability Checking of Contracts using Theories --- *)
(* --- Machine-Checked Proofs For Realizability Checking Algorithms --- *)

Inductive id : Type :=
Id : nat -> id.

Inductive inputs : Type :=
input : id -> nat -> inputs.

Inductive state : Type :=
st : id -> nat -> state.

Definition initial := state -> Prop.

Definition transition := state -> inputs -> state -> Prop.

Definition iguarantee := state -> Prop.

Definition tguarantee := state -> inputs -> state -> Prop.

Definition assumption := state -> inputs -> Prop.

Inductive reachable (s:state) (init: initial) (t: transition) (a:assumption) : Prop :=
rch : ((init s) \/ (exists (s':state) (inp:inputs), 
                          (reachable s' init t a) /\ (a s' inp) /\ (t s' inp s))) ->
       reachable s init t a.

Inductive realization (init : initial) (t : transition) (a:assumption) (gi:iguarantee) (gt: tguarantee) : Prop :=
real : ((forall (s:state), (init s) -> (gi s)) /\
       (forall (s s':state) (inp : inputs), 
          ((reachable s init t a) /\ (a s inp) /\ (t s inp s')) -> gt s inp s') /\
       (exists (s:state), init s) /\
       (forall (s:state) (inp:inputs), (reachable s init t a /\ (a s inp)) -> 
         (exists (s':state), t s inp s')))->
       realization init t a gi gt.

Inductive realizable_contract (a:assumption) (gi: iguarantee) (gt: tguarantee) : Prop :=
rc : (exists (init : initial) (t : transition), realization init t a gi gt) -> realizable_contract a gi gt.

CoInductive viable (s:state) (a:assumption) (gi:iguarantee) (gt: tguarantee) : Prop :=
vbl : (forall (i:inputs), (a s i) -> (exists (s':state), gt s i s' /\ viable s' a gi gt)) -> viable s a gi gt.

Inductive realizable (a:assumption) (gi : iguarantee) (gt:tguarantee) : Prop :=
rl : (exists (s:state), gi s /\ viable s a gi gt) -> realizable a gi gt.


Lemma init_reachable : forall (s:state) (init:initial) (t:transition) (a:assumption),
init s -> reachable s init t a.
Proof. intros. apply rch. left. apply H. Qed.


Lemma reachable_viable : forall (s :state) (init:initial) (t:transition) (a:assumption) (gi:iguarantee) (gt:tguarantee),
realization init t a gi gt -> reachable s init t a -> viable s a gi gt.

Proof. cofix. intros. apply vbl. intros. inversion H. inversion H2. inversion H4. inversion H6. destruct H8 with (s:=s) (inp:=i). split. apply H0. apply H1. exists x. split. apply H5.
  split. apply H0. split. apply H1. apply H9. apply reachable_viable with (init:= init) (t:=t). apply H. apply rch. right. exists s. exists i. split. apply H0. split. apply H1. apply H9.
Qed.


Theorem realcontract_implies_real  (init:initial) (t:transition) : forall (a : assumption) (gi : iguarantee) (gt : tguarantee),
realizable_contract a gi gt -> realizable a gi gt.
Proof.
  split.
  intros. apply rl. inversion H. inversion H0. inversion H1. inversion H2. inversion H3.
  inversion H5. inversion H7. inversion H8. exists x1. apply and_comm. split. apply init_reachable with (s:= x1) (t:=x0) (a:=a) in H10. apply reachable_viable with (gi:=gi) (gt:= gt) in H10. apply H10.
  apply H2. apply H4. apply H10.
Qed.

Theorem reach_via : forall (s s0:state) (a:assumption) (gi:iguarantee) (gt:tguarantee),
viable s0 a gi gt -> reachable s (fun s => s = s0) (fun s i s' => gt s i s' /\ viable s' a gi gt) a -> viable s a gi gt.
Proof.
  intros. inversion H0. inversion H1. subst. assumption. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8. assumption.
Qed.

Theorem real_implies_realcontract (init:initial) (t:transition) : forall (a : assumption) (gi : iguarantee) (gt : tguarantee),
realizable a gi gt -> realizable_contract a gi gt.
Proof.
  intros. apply rc. inversion H as [[s0 [gi_s0 viable_s0]]]. exists (fun s => s = s0).
  exists (fun s i s' => gt s i s' /\ viable s' a gi gt). apply real. split.
  
  intros. rewrite H0. apply gi_s0.

  split. intros. inversion H0. inversion H2. inversion H4. apply H5.

  split. exists s0. reflexivity.
  
  intros. inversion H0. apply reach_via with (gi:=gi) (gt:=gt) in H1. inversion H1. apply H3. apply H2. assumption.
Qed.

Fixpoint finite_viable (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => True
  | S n' => forall i, a s i -> exists s', gt s i s' /\ finite_viable n' s' a gt
  end.


Fixpoint extendable (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => forall i, a s i -> exists (s':state), gt s i s'
  | S n' => forall i s', a s i -> gt s i s' -> extendable n' s' a gt
  end.

Definition Basecheck (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) :=
exists (s:state), (gi s /\ finite_viable n s a gt).


Definition Extendcheck (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable n s a gt.


Lemma viable_implies_finite_viable : forall a gi gt n s,
viable s a gi gt -> finite_viable n s a gt.
Proof. intros a gi gt n. induction n. intros. simpl. auto.
  intros. simpl. intros.  inversion H. apply H1 in H0.
  inversion H0. inversion H2. exists x.
  intros. split. apply H3. apply IHn. apply H4.
Qed.

Theorem unrealizable_soundness : forall (s:state) (init:initial) (t:transition) a gi gt,
(exists n, ~Basecheck n a gi gt) -> ~ realizable_contract a gi gt.
Proof.
  intros. unfold not. intros. apply realcontract_implies_real in H0. inversion H0. inversion H1. inversion H2. inversion H. apply viable_implies_finite_viable with (n:=x0) in H4.
  apply H5. unfold Basecheck. exists x. split. assumption. assumption. apply init. apply t.
Qed.


Lemma finite_viable_plus_one : forall n a gt (gi:iguarantee) (i:inputs) s,
(extendable n s a gt /\ finite_viable n s a gt) -> finite_viable (S n) s a gt.
Proof. intros n a gt gi i. induction n.
  intros. simpl. intros. inversion H. simpl in H1. apply H1 in H0.
  inversion H0. exists x. intros. auto.
  
  intros. simpl. intros. inversion H. assert (H3: a s i0).
  apply H0. simpl in H2. simpl in H1. apply H2 in H3. inversion H3.
  exists x. intros. split. inversion H4. apply H5.
  assert (H5: extendable n x a gt). apply H1 with (i:=i0).
  apply H0. inversion H4. apply H5. inversion H4.
  apply conj with (A:=extendable n x a gt) in H7.
  apply IHn in H7. simpl in H7. intros. apply H7 in H8.
  apply H8. apply H5.
Qed.

Lemma extend_viable_shift : forall (n : nat) (a : assumption) (gi : iguarantee) (gt : tguarantee) (s : state) (i : inputs),
(extendable n s a gt /\ finite_viable n s a gt /\ a s i) -> (exists s', gt s i s' /\ finite_viable n s' a gt).
Proof. intros n a gi gt. induction n.
  intros. inversion H. simpl in H0. inversion H1.
  apply H0 in H3. inversion H3. exists x. intros. simpl. auto.
  
  intros. inversion H. simpl in H0. inversion H1. assert (H4: a s i).
  apply H3. simpl in H2. apply H2 in H3. inversion H3.
  exists x. intros. simpl. intros.
  assert (H8: a s i -> gt s i x -> extendable n x a gt).
  apply H0. apply H8 in H4. inversion H5.
  split. apply H6. intros. apply conj with (A:=extendable n x a gt) in H7.
  apply finite_viable_plus_one in H7. simpl in H7. apply H7. apply H9.
  apply gi. apply i. apply H4. inversion H5. apply H6.
Qed.

Lemma fv_ex_implies_viable : forall n (a:assumption) gi gt (init:initial) (t:transition) (s:state),
(finite_viable n s a gt /\ Extendcheck n a gt) -> viable s a gi gt.
Proof.
 cofix. intros n a gi gt init t. intros. apply vbl.
 intros. inversion H. unfold Extendcheck in H2.
 assert (H3: extendable n s a gt). apply H2.
 apply conj with (A:=finite_viable n s a gt) in H0.
 apply conj with (A:= extendable n s a gt) in H0.
 apply extend_viable_shift in H0. inversion H0.
 exists x. inversion H4. split. apply H5.
 apply fv_ex_implies_viable with (n:=n). apply init.
 apply t. split. apply H6. inversion H. apply H8.
 apply gi.  apply H3. apply H1.
Qed.

Theorem realizable_soundness : forall (s:state) (init:initial) (t:transition) a gi gt,
(exists n, (Basecheck n a gi gt /\ Extendcheck n a gt)) -> realizable_contract a gi gt.
Proof.
  intros. apply real_implies_realcontract. apply init. apply t. apply rl.
  inversion H. inversion H0. inversion H1. subst. inversion H3. unfold Basecheck in H4.
  exists x0. split. assumption. apply fv_ex_implies_viable with (n:=x). apply gi. apply t. split.
  assumption. assumption.
Qed.

Definition Basecheck_simple (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable n s a gt.

Theorem basecheck_soundness_one_way : forall n a (gi:iguarantee) gt (i:inputs),
((exists s, gi s) /\
(forall k, (k<=n) -> Basecheck_simple k a gi gt)) -> Basecheck n a gi gt.
Proof.
  intros. induction n. unfold Basecheck. assert (H0: 0<=0). apply le_n. 
  inversion H. inversion H1. exists x. split. assumption. constructor.

  unfold Basecheck. inversion H.
  assert (H3: (forall k : nat, k <= n -> Basecheck_simple k a gi gt)).
  intros. apply le_S in H2. inversion H. apply H4 in H2.
  assumption. apply conj with (A:= exists s : state, gi s) in H3.
  apply IHn in H3. inversion H3. inversion H2.
  exists x. split. assumption.
  
  apply finite_viable_plus_one. assumption. assumption. split. unfold Basecheck_simple in H1.
  apply H1. apply le_S. apply le_n. assumption. assumption.
  assumption.
Qed.

(* --- Synthesis from Assume-Guarantee Contracts using Skolemized Proofs of Realizability --- *)

Definition skolem_0 (s:state) (i:inputs) : state := admit.
Definition skolem_1 (s:state) (i: inputs) (s': state) (i': inputs) : state := admit.

Inductive extendable_f : nat -> state -> assumption -> tguarantee -> Prop :=
|exnill : forall s (a:assumption) (gt:tguarantee), (forall i, a s i -> (gt s i (skolem_0 s i))) ->
extendable_f O s a gt
|exone : forall s i (a:assumption) (gt:tguarantee), a s i /\ gt s i (skolem_0 s i) /\ 
   (forall s' i', a s' i' -> gt s' i' (skolem_1 s i s' i')) -> extendable_f (S O) s a gt.


Theorem extf_zero_implies_ext_zero : forall (a:assumption) (gt:tguarantee) (s:state),
extendable_f O s a gt -> extendable O s a gt.
Proof.
  intros n a gt.
  intros. inversion H. simpl. intros. exists (skolem_0 s i).
  apply H0. apply H1.
Qed.

Theorem extf_one_implies_ext_one : forall (a:assumption) (gt:tguarantee) (s:state),
extendable_f 1 s a gt -> extendable 1 s a gt.
Proof.
  intros. simpl. intros. inversion H. inversion H3. inversion H8.
  assert (H11: gt s' i0 (skolem_1 s i1 s' i0)).
  apply H10. apply H2.  exists (skolem_1 s i1 s' i0).  apply H11. 
Qed.

Definition Basecheck_simple_f (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable_f n s a gt.

Definition Extendcheck_f (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable_f n s a gt.

Theorem BCheck_f_imp_BCheck_zero : forall (a:assumption) (gi:iguarantee) (gt:tguarantee),
Basecheck_simple_f O a gi gt -> Basecheck_simple O a gi gt.
Proof.
  intros. unfold Basecheck_simple_f in H. unfold Basecheck_simple.
  intros. apply extf_zero_implies_ext_zero. apply H. apply H0.
Qed.

Theorem BCheck_f_imp_BCheck_one : forall (a:assumption) (gi:iguarantee) (gt:tguarantee),
Basecheck_simple_f 1 a gi gt -> Basecheck_simple 1 a gi gt.
Proof.
  intros. unfold Basecheck_simple_f in H. unfold Basecheck_simple.
  intros. apply H in H0. simpl. intros. inversion H0. inversion H4. inversion H9.
  assert (H12: gt s' i0 (skolem_1 s i1 s' i0)). apply H11. assumption.
  exists (skolem_1 s i1 s' i0). apply H12.
Qed.

Theorem ECheck_f_imp_ECheck_zero : forall (a:assumption) (gt:tguarantee) (s:state),
Extendcheck_f O a gt -> Extendcheck O a gt.
Proof.
  intros. unfold Extendcheck. unfold Extendcheck_f in H.
  intros. apply extf_zero_implies_ext_zero. apply H.
Qed.

Theorem ECheck_f_imp_ECheck_one : forall (a:assumption) (gt:tguarantee) (s:state),
Extendcheck_f 1 a gt -> Extendcheck 1 a gt.
Proof.
  intros. unfold Extendcheck. unfold Extendcheck_f in H.
  intros. apply extf_one_implies_ext_one. apply H.
Qed.

(*Random Notes Below --- Safe to ignore! *)

(*

Inductive extendable_f : nat -> assumption -> tguarantee -> Prop :=
|exnill : forall sl s (a:assumption) (gt:tguarantee), (sl = scons s snil) /\ (forall i, a s i -> (gt s i (skolem s i))) ->
extendable_f O sl a gt
|exone : forall sl s s' (a:assumption) (gt:tguarantee), extendable_f O sl a gt /\ (forall i, a s' i -> gt s i (skolem




Fixpoint extendable_f (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => forall i, a s i -> gt s i (skolem_0 s i)
  | S O => forall (i:inputs) s', a s i  /\ s' = skolem_0 s i -> gt s i (skolem s i) -> extendable_f n' s' a gt
  end.



Theorem extf_zero_implies_ext_zero : forall (a:assumption) (gt:tguarantee) (s:state),
extendable_f O s a gt -> extendable O s a gt.
Proof.
  intros n a gt.
  intros. inversion H. simpl. intros. exists (skolem_0 s i).
  apply H0. apply H1.
Qed.

Theorem extf_one_implies_ext_one : forall (a:assumption) (gt:tguarantee) (s:state),
extendable_f 1 s a gt -> extendable 1 s a gt.
Proof.
  intros. simpl. intros. simpl in H.

 simpl in H1. intros. 
  apply H1 in H2. exists (skolem s i). apply H2.

  intros. simpl. inversion H. intros. apply IHn.
  split. apply H0. simpl in H1. apply H1 with (i:=i).
  split. apply H2. apply H0. assert (H4: s' = skolem s i).
  apply H0. rewrite H4 in H3. apply H3.
Qed.

Definition Basecheck_simple_f_zero (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable_f O s a gt.

Definition Basecheck_simple_f_one (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable_f 1 s a gt.

Definition Extendcheck_f_zero (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable_f O s a gt.

Definition Extendcheck_f_one (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable_f 1 s a gt.

Theorem BCheck_f_imp_BCheck : forall (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) (sl:statelist),
Basecheck_simple_f O a gi gt -> Basecheck_simple O a gi gt.
Proof.
  intros. unfold Basecheck_simple_f in H. unfold Basecheck_simple.
  intros. apply exs_imp_ex_one. apply sl. apply H. apply H0.
Qed.



Inductive statelist : Type :=
|snil : statelist
|scons : state -> statelist -> statelist.

Inductive extendable_f : nat -> statelist -> assumption -> tguarantee -> Prop :=

|exnill : forall sl s (a:assumption) (gt:tguarantee), (sl = scons s snil) /\ (forall i, a s i -> (gt s i (skolem s i))) ->
extendable_f O sl a gt
|exone : forall sl s s' (a:assumption) (gt:tguarantee), extendable_f O sl a gt /\ (forall i, a s' i -> gt s i (skolem
|exind : forall m sl a gt i s sl', ((sl = scons s sl') /\ a s i /\ gt s i (skolem s i) /\ extendable_f m sl a gt) -> extendable_f (S m) (scons (skolem s i) sl) a gt.



Inductive statelist : Type :=
|snil : statelist
|scons : state -> inputs -> statelist -> statelist.



Definition skolem (s:state) (i:inputs) : state := admit.


Fixpoint extendable_f (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => forall i, a s i -> gt s i (skolem s i)
  | S n' => forall (i:inputs) s', a s i  /\ s' = skolem s i -> gt s i (skolem s i) -> extendable_f n' s' a gt
  end.

Fixpoint finite_viable_f (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => True
  | S n' => forall i, a s i -> gt s i (skolem s i) /\ finite_viable_f n' (skolem s i) a gt
  end.


CoInductive viable_f (s:state) (a:assumption) (gi:iguarantee) (gt: tguarantee) : Prop :=
vblf : (forall (i:inputs), a s i -> gt s i (skolem s i) /\ viable_f (skolem s i) a gi gt) -> viable_f s a gi gt.


Theorem viable_f_implies_viable : forall s a gi gt,
(viable_f s a gi gt -> viable s a gi gt).
Proof. cofix.
  intros. inversion H. apply vbl. intros. apply H0 in H1.
  exists (skolem s i). inversion H1. split. apply H2. apply viable_f_implies_viable.
  apply H3.
Qed.

Definition Basecheck_simple_f (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable_f n s a gt.

Definition Extendcheck_f (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable_f n s a gt.


Theorem exs_imp_ex_one : forall (n:nat)  (a:assumption) (gt:tguarantee) (s:state),
(forall s' i' s'', s'' = skolem s' i') /\ extendable_f n s a gt -> extendable n s a gt.
Proof.
  intros n a gt. induction n.
  intros. inversion H. simpl. simpl in H1. intros. 
  apply H1 in H2. exists (skolem s i). apply H2.

  intros. simpl. inversion H. intros. apply IHn.
  split. apply H0. simpl in H1. apply H1 with (i:=i).
  split. apply H2. apply H0. assert (H4: s' = skolem s i).
  apply H0. rewrite H4 in H3. apply H3.
Qed.

Lemma finite_viable_plus_one_f : forall n a gt (gi:iguarantee) (i:inputs) s,
(forall s' i' s'', s'' = skolem s' i') /\ extendable_f n s a gt /\ finite_viable_f n s a gt -> finite_viable_f (S n) s a gt.
Proof.
  intros n a gt gi i. induction n. intros.
  simpl. intros. inversion H. split. inversion H2. simpl in H3. apply H3.
  apply H0. auto.

  intros. inversion H. inversion H1. simpl in H2. simpl in H3.
  simpl. intros. assert (H5: a s i0). apply H4.
  assert (s':state). apply s. assert (H6: s' = skolem s i0).  
  apply H0. split. apply conj with (A:=a s i0) in H6. apply H2 in H6.
  apply H3 in H4. inversion H4. apply H7.
  apply H3 in H4. inversion H4. apply H7.
  apply H4.
  intros. assert (s' = skolem s i0). apply H0.
  apply conj with (A:=a s i0) in H6. apply H2 in H6.
  rewrite H8 in H6. apply H3 in H4. inversion H4. 
  assert (H11:finite_viable_f (S n) (skolem s i0) a gt). 
  apply IHn. split. apply H0. split. apply H6. apply H10.
  admit. admit. assumption. Qed.



Theorem extendable_f_imp_viable_f : forall  (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) (s:state),
(forall i, a s i /\ finite_viable_f n s a gt /\ Extendcheck_f n a gt) -> viable_f s a gi gt.
Proof.
  cofix. intros n a gi gt. induction n.
  intros. apply vblf. intros. split. assert (H1: a s i /\ finite_viable_f 0 s a gt /\ Extendcheck_f 0 a gt).
  apply H. inversion H1. inversion H3. unfold Extendcheck_f in H5. assert (H6: extendable_f 0 s a gt).
  apply H5. simpl in H6. apply H6. apply H2. admit. admit.
Qed.


Inductive statelist : Type :=
|snil : statelist
|scons : state -> inputs -> statelist -> statelist.
 

Fixpoint skolem (s:state) (i:inputs) (sl:statelist) (a:assumption) (gt:tguarantee): Prop := 
  match sl with
  |snil => a s i /\ exists s':state, gt s i s'
  |scons s' i' sl' => a s' i' -> gt s' i' s -> a s i -> exists s'', gt s i s'' -> skolem s' i' sl' a gt
  end.



Fixpoint extendable_f (n:nat) (s:state) (a:assumption) (gt:tguarantee): Prop :=
  match n with
  | O => forall i sl, a s i -> skolem s i sl a gt
  | S n' => forall i sl s', skolem s i sl a gt -> gt s i s' -> extendable_f n' s' a gt
  end.

Fixpoint finite_viable_f (n:nat) (s:state) (a:assumption) (gt:tguarantee) : Prop :=
  match n with
  | O => True
  | S n' => forall i sl, a s i -> exists s', skolem s i sl a gt -> gt s i s' /\ finite_viable_f n' s' a gt
  end.


CoInductive viable_f (s:state) (a:assumption) (gi:iguarantee) (gt: tguarantee) : Prop :=
vblf : (forall (i:inputs) (sl:statelist) s', a s i -> skolem s i sl a gt /\ gt s i s' /\ viable_f s' a gi gt) -> viable_f s a gi gt.

Theorem viable_f_implies_viable : forall s a gi gt (sl:statelist),
(viable_f s a gi gt -> viable s a gi gt).
Proof. cofix.
  intros. inversion H. apply vbl. intros. assert (x:state). apply s.
  destruct H0 with (i:=i) (sl:=sl) (s':=x). apply H1. inversion H3. exists x.
  split. apply H4. apply viable_f_implies_viable. apply sl. apply H5.
Qed.


Definition Basecheck_simple_f (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee):=
forall s, (gi s) -> extendable_f n s a gt.

Definition Extendcheck_f (n:nat) (a:assumption) (gt:tguarantee) :=
forall s a gt, extendable_f n s a gt.

Theorem exs_imp_ex_one : forall (n:nat)  (a:assumption) (gt:tguarantee) (sl:statelist) (s:state),
extendable_f n s a gt -> extendable n s a gt.
Proof.
  intros n a gt sl. induction n. induction sl. intros.
  simpl. intros. simpl in H. apply H with (sl:=snil) in H0.
  simpl in H0. inversion H0. inversion H2. exists x. apply H3.  
  intros. apply IHsl. apply H.

  induction sl. intros. simpl. intros. apply IHn. simpl in H. apply H with (i:=i) (sl:=snil).
  simpl. split. apply H0. exists s'. apply H1. apply H1.
  intros. apply IHsl. apply H.
Qed.

Theorem BCheck_f_imp_BCheck : forall (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) (sl:statelist),
Basecheck_simple_f n a gi gt -> Basecheck_simple n a gi gt.
Proof.
  intros. unfold Basecheck_simple_f in H. unfold Basecheck_simple.
  intros. apply exs_imp_ex_one. apply sl. apply H. apply H0.
Qed.

Theorem ECheck_f_imp_ECheck : forall (n:nat) (a:assumption) (gt:tguarantee) (sl:statelist) (s:state) (sl:statelist),
Extendcheck_f n a gt -> Extendcheck n a gt.
Proof.
  intros. unfold Extendcheck. unfold Extendcheck_f in H.
  intros. apply exs_imp_ex_one. apply sl. apply H.
Qed.


Theorem extendable_f_imp_viable_f : forall  (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) (s:state),
(forall i, a s i /\ finite_viable_f n s a gt /\ Extendcheck_f n a gt) -> viable_f s a gi gt.
Proof.
  cofix. intros. apply vblf. intros.
  destruct H with (i:=i). unfold Extendcheck_f in H2. inversion H2.
  assert (H4: extendable_f n s a gt). apply H3. induction n. simpl in H4.
  apply H4 with (sl:=sl) in H0. split. apply H0. split. induction sl.
  simpl in H0. inversion H0. apply H6.
 assert (H4: extendable_f 0 s a gt).
  apply H1. simpl in H4. split. apply H4. apply H4 in 
 cofix. intros. apply vblf. induction n.
  intros. split.








 induction intros. inversion H. assert (H10: a s i). assumption. apply conj with (A:=finite_viable_f 0 s a gt) in H0.
 unfold Extendcheck_f in H2. assert (H3: extendable_f 0 s a gt). apply H2. apply conj with (A:= extendable_f 0 s a gt) in H0.
 apply extend_f_viable_f_shift in H0. inversion H3. apply H4 in H10. apply if_skolem_then_gt_holds in H10. 
 inversion H10.  exists x. split.  inversion H5. assumption. split. inversion H5. assumption.
 apply extendable_f_imp_viable_f. split. apply fvnill. unfold Extendcheck_f.
 intros. apply H2. assumption. assumption. assumption. assumption.
Qed.


Lemma extend_f_viable_f_shift : forall (n:nat) (a:assumption) (gi:iguarantee) (gt:tguarantee) (s:state) (i:inputs),
(extendable_f n s a gt /\ finite_viable_f n s a gt /\ a s i) -> forall i' (sl:statelist), exists s', (skolem s' i' (scons s i sl) a gt) /\ finite_viable_f n s' a gt.
Proof.
  intros n a gi gt. induction n.
  intros. inversion H. simpl in H0. 
  inversion H1. apply H0 with (sl:=sl) in H3.
  induction sl. simpl in H3. inversion H3. inversion H5.
  exists x. split. simpl. intros. assert (s'':state).
  apply s. exists s''. intros. split. apply H4. exists x. apply H6.
  simpl. auto.

  apply IHsl.
 simpl in H0. inversion H1. 
  apply H0 with(sl:=snil) in H3. simpl in H3.
  inversion H3. inversion H5. exists x. intros.
  split. simpl. intros. assert (s'':state). apply s.
  exists s''. intros. apply H3. simpl. auto.

  intros. apply IHsl in H. inversion H. exists x. intros.
  simpl. intros. split. intros. assert (s'':state). apply s. 
  exists s''. intros.
 split. simpl. intros. intros.
 split. inversion H. simpl in H0.(sl:statelist) 
  simpl.
  induction sl. simpl.
  simpl. split. split. inversion H1. apply H3. split.
  assert (H2: skolem s i sl a gt). apply H0. inversion H1. apply H3.
  induction sl. simpl in H2.  inversion H2.
  simpl in H2. apply H0 with (sl:=(scons s i sl)). inversion H1. apply H3. simpl. auto.
  
  intros. split. simpl. split.
  inversion H. simpl in H0. inversion H1. simpl in H2. apply H2 with (s':=s') (sl:=sl) in H3.
  assert (H4: skolem s i (scons s' i' sl) a gt /\ finite_viable_f n s' a gt).
  apply H0.
  apply IHn. inversion H. simpl in H0.
  assert (H2: skolem s i sl a gt /\ gt s i s' /\ extendable_f n s a gt).
  apply H0.
  



 inversion H. inversion H1. exists s.
  inversion H0. apply H2. inversion H1. apply H8.
  apply IHn. split. inversion H. inversion H2. inversion H5.
  apply H10. split. inversion H1. inversion H2. apply H5.
  inversion H1. apply H3. inversion H0. inversion H3. apply H8.
  inversion H1. inversion H2. split. apply H5. apply H3.

  induction n. apply fvnill. apply fvv. apply IHn. inversion H0.
  inversion H3. split. apply H8. split. inversion H. inversion H11.
  inversion H12. apply H15. inversion H1. apply H11.
  inversion H0. inversion H3. apply H8. inversion H1.
  inversion H2. split. apply H5. apply H3.
  intros. inversion H0. inversion H4.
  assert (H12: compatible_f sl s i a gt /\ gt (extendable_f 0 (skolem (hds s sl) (hdi i sl) sl) sl a gt).
  inversion H4. apply H10. inversion H12. inversion H10. apply H11. inversion H9.
   inversion H11. destruct H10.

apply fvv.

 inversion H0. inversion H1. split. 
  apply H2. apply H9. apply fvnill.
  split. 
  split.  inversion H2. inversion H8. apply H10. inversion H1. apply H17.
apply H2 in H7. apply if_skolem_then_gt_holds in H7.
  inversion H7. exists x. inversion H8. split. assumption. apply fvv. assumption. assumption. assumption.
Qed.


Theorem extendable_f_imp_viable_f : forall (s:state) (a:assumption) (gi:iguarantee) (gt:tguarantee),
(finite_viable_f O s a gt /\ Extendcheck_f O a gt) -> viable_f s a gi gt.
Proof.
 cofix. intros. apply vblf. intros. inversion H. assert (H10: a s i). assumption. apply conj with (A:=finite_viable_f 0 s a gt) in H0.
 unfold Extendcheck_f in H2. assert (H3: extendable_f 0 s a gt). apply H2. apply conj with (A:= extendable_f 0 s a gt) in H0.
 apply extend_f_viable_f_shift in H0. inversion H3. apply H4 in H10. apply if_skolem_then_gt_holds in H10. 
 inversion H10.  exists x. split.  inversion H5. assumption. split. inversion H5. assumption.
 apply extendable_f_imp_viable_f. split. apply fvnill. unfold Extendcheck_f.
 intros. apply H2. assumption. assumption. assumption. assumption.
Qed.
*)