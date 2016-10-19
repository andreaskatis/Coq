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

Inductive reachable (s : state) (init : initial) (t : transition) (a : assumption) : Prop :=
rch : ((init s) \/
      (exists (s' : state) (inp : inputs),(reachable s' init t a) /\ (a s' inp) /\ (t s' inp s))) ->
       reachable s init t a.

Inductive realization (init : initial) (t : transition) (a : assumption) (gi : iguarantee) (gt : tguarantee) : Prop :=
real : ((forall (s : state), (init s) -> (gi s)) /\
       (forall (s s' : state) (inp : inputs), 
          ((reachable s init t a) /\ (a s inp) /\ (t s inp s')) -> gt s inp s') /\
       (exists (s : state), init s) /\
       (forall (s : state) (inp:inputs), (reachable s init t a /\ (a s inp)) -> 
         (exists (s' : state), t s inp s'))) ->
       realization init t a gi gt.

Inductive realizable_contract (a : assumption) (gi : iguarantee) (gt : tguarantee) : Prop :=
rc : (exists (init : initial) (t : transition), realization init t a gi gt) -> realizable_contract a gi gt.

CoInductive viable (s : state) (a : assumption) (gi : iguarantee) (gt : tguarantee) : Prop :=
vbl : (forall (i : inputs), (a s i) -> (exists (s' : state), gt s i s' /\ viable s' a gi gt)) -> viable s a gi gt.

Inductive realizable (a : assumption) (gi : iguarantee) (gt : tguarantee) : Prop :=
rl : (exists (s : state), gi s /\ viable s a gi gt) -> realizable a gi gt.


Lemma init_reachable : forall (s:state) (init : initial) (t : transition) (a : assumption),
init s -> reachable s init t a.
Proof. intros. apply rch. left. apply H. Qed.


Lemma reachable_viable : forall (s : state) (init : initial) (t : transition) (a : assumption) (gi : iguarantee) (gt : tguarantee),
realization init t a gi gt -> reachable s init t a -> viable s a gi gt.

Proof. cofix. intros. apply vbl. intros. inversion H.
inversion H2. inversion H4. inversion H6. destruct H8 with (s:=s) (inp:=i). 
  split.
    apply H0. apply H1. exists x. split.
      apply H5. split.
        apply H0. split.
          apply H1.
          apply H9.
      apply reachable_viable with (init:= init) (t:=t). 
        apply H.
        apply rch. right. exists s. exists i. split.
          apply H0. split.
            apply H1. 
            apply H9.
Qed.


Theorem realcontract_implies_real  (init : initial) (t : transition) : forall (a : assumption) (gi : iguarantee) (gt : tguarantee),
realizable_contract a gi gt -> realizable a gi gt.
Proof.
  intros. apply rl. inversion H. inversion H0. inversion H1. inversion H2. inversion H3.
  inversion H5. inversion H7. inversion H8. exists x1. apply and_comm. split. apply init_reachable with (s:= x1) (t:=x0) (a:=a) in H10. apply reachable_viable with (gi:=gi) (gt:= gt) in H10. apply H10.
  apply H2. apply H4. apply H10.
Qed.

Theorem reach_via : forall (s s0 : state) (a : assumption) (gi : iguarantee) (gt : tguarantee),
viable s0 a gi gt -> reachable s (fun s => s = s0) (fun s i s' => gt s i s' /\ viable s' a gi gt) a -> viable s a gi gt.
Proof.
  intros. inversion H0. inversion H1. subst. assumption. inversion H2. inversion H3. inversion H4. inversion H6. inversion H8. assumption.
Qed.

Theorem real_implies_realcontract (init : initial) (t : transition) : forall (a : assumption) (gi : iguarantee) (gt : tguarantee),
realizable a gi gt -> realizable_contract a gi gt.
Proof.
  intros. apply rc. inversion H as [[s0 [gi_s0 viable_s0]]]. exists (fun s => s = s0).
  exists (fun s i s' => gt s i s' /\ viable s' a gi gt). apply real. split.
  
  intros. rewrite H0. apply gi_s0.

  split. intros. inversion H0. inversion H2. inversion H4. apply H5.

  split. exists s0. reflexivity.
  
  intros. inversion H0. apply reach_via with (gi:=gi) (gt:=gt) in H1. inversion H1. apply H3. apply H2. assumption.
Qed.


Inductive finite_viable : nat -> state -> assumption -> tguarantee -> Prop :=
|fvnil : forall s a gt, finite_viable O s a gt
|fv : forall m s a gt, finite_viable m s a gt -> (forall (i : inputs), a s i -> (exists s', gt s i s')) -> finite_viable (S m) s a gt.


Inductive extendable : nat -> state -> assumption -> tguarantee -> Prop :=
| exnil : forall s (a : assumption) gt, (forall i, a s i -> exists s', gt s i s') ->
extendable O s a gt
| ex : forall m s a gt, (forall i s', a s i /\ gt s i s' /\ extendable
m s' a gt) -> extendable (S m) s a gt.

Definition Basecheck (n : nat) (a : assumption) (gi : iguarantee) (gt : tguarantee) :=
exists (s : state), (gi s /\ finite_viable n s a gt).

Definition Extendcheck n (a : assumption) (gt : tguarantee) :=
forall s a gt, extendable n s a gt.

Lemma viable_implies_finite_viable : forall s a gi gt n,
viable s a gi gt -> finite_viable n s a gt.
Proof.
  intros. induction n. simpl. intros.  inversion H. constructor.
   inversion H. apply fv. apply IHn. intros. destruct H0 with (i:=i). assumption. exists x. inversion H2. assumption.
Qed.

Theorem unrealizable_soundness : forall (init : initial) (t : transition) a gi gt,
(exists n, ~Basecheck n a gi gt) -> ~ realizable_contract a gi gt.
Proof.
  intros. unfold not. intros. apply realcontract_implies_real in H0. inversion H0. inversion H1. inversion H2. inversion H. apply viable_implies_finite_viable with (n:=x0) in H4.
  apply H5. unfold Basecheck. exists x. split. assumption. assumption. apply init. apply t.
Qed.

Lemma extend_viable_shift : forall (s : state) (n : nat) (i : inputs) (a : assumption) (gi : iguarantee) (gt : tguarantee),
(extendable n s a gt /\ finite_viable n s a gt /\ a s i) -> (exists s', gt s i s' /\ finite_viable n s' a gt).
Proof.
  intros. induction n. inversion H. inversion H0. destruct H2 with (i:=i). inversion H1. assumption.
  exists x. split. assumption. constructor.
  
  inversion H. inversion H1. inversion H0. destruct H5 with (i:=i) (s':=s). exists s.
  inversion H10. split. assumption. assumption.
Qed.

Lemma fv_ex_implies_viable : forall (s : state) n (a : assumption) gi gt,
(finite_viable n s a gt /\ Extendcheck n a gt) -> viable s a gi gt.
Proof.
 cofix. intros. apply vbl. inversion H. unfold Extendcheck in H1.
 intros. apply conj with (A:= finite_viable n s a gt) in H2.
 apply conj with (A:= extendable n s a gt) in H2.
 apply extend_viable_shift in H2. destruct H2.
 inversion H2. exists x. split. assumption.
 apply fv_ex_implies_viable with (n:=n).
 split. assumption. unfold Extendcheck. assumption.
 apply gi. apply H1. inversion H. assumption.
Qed.

Theorem realizable_soundness : forall (init : initial) (t : transition) a gi gt,
(exists n, (Basecheck n a gi gt /\ Extendcheck n a gt)) -> realizable_contract a gi gt.
Proof.
  intros. apply real_implies_realcontract. apply init. apply t. apply rl.
  inversion H. inversion H0. inversion H1. inversion H3.
  exists x0. split. assumption. apply fv_ex_implies_viable with (n:=x). split.
  assumption. assumption.
Qed.

Lemma finite_viable_plus_one : forall s n a gt (gi : iguarantee) (i : inputs),
(extendable n s a gt /\ finite_viable n s a gt) -> finite_viable (S n) s a gt.
Proof.
  intros. induction n. apply fv. constructor. inversion H. inversion H0.
  intros. apply H2 in H3. assumption.

  apply fv. apply IHn. split. inversion H. inversion H0.
  destruct H3 with (i:=i) (s':=s). inversion H8. assumption.
  inversion H. inversion H1. assumption.
  intros. inversion H.
  inversion H2. apply H5 in H0. apply H0.
Qed.

Definition Basecheck_simple (n : nat) (a : assumption) (gi : iguarantee) (gt : tguarantee):=
forall s, (gi s) -> extendable n s a gt.

Theorem basecheck_soundness_one_way : forall n a (gi : iguarantee) gt (i : inputs),
((exists s, gi s) /\
(forall k, (k<=n) -> Basecheck_simple k a gi gt)) -> Basecheck n a gi gt.
Proof.
  intros. induction n. inversion H. inversion H0. unfold Basecheck. exists x. split. assumption. constructor.

  unfold Basecheck. inversion H.
  assert (H3: (forall k : nat, k <= n -> Basecheck_simple k a gi gt)).
  intros. apply le_S in H2. apply H1. assumption.
  apply conj with (A:= exists s : state, gi s) in H3.
  apply IHn in H3. inversion H3. inversion H2.
  exists x. split. assumption.
  
  apply finite_viable_plus_one. apply gi. apply i. split. unfold Basecheck_simple in H1.
  apply H1. apply le_S. apply le_n. assumption. assumption.
  assumption.
Qed.

Definition witness (i:inputs) (n:nat) (s:state) (a:assumption) (gi: iguarantee) (gt: tguarantee) :=
forall i s k n, (k<=n -> (a s i) /\ exists s', gt s i s') /\ extendable (S n) s a gt.

Theorem asd : forall i n a gi gt, (Basecheck n a gi gt /\ Extendcheck n a gt) -> exists s, witness i n s a gi gt.
intros.
  inversion H. inversion H0. exists x. inversion H2. assert (H5: extendable n x a gt). apply H1. unfold witness.
  intros. split. intros.