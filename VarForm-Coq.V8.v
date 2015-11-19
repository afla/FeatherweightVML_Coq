Require Import Coq.Arith.Peano_dec
               Coq.Arith.EqNat
               Coq.Lists.List.
Import ListNotations.

Notation "a && b" := (andb a b).
Notation "a || b" := (orb a b).
Notation "! a" := (negb a) (at level 5).



Definition Object := nat.
Definition ObjectSet := list Object.


Inductive Link := link : nat -> Object -> Object -> Link.
Definition LinkSet := list Link.
Notation "id ¤ src --> tgt" := (link id src tgt) (at level 66).


Inductive Graph := graph : ObjectSet -> LinkSet -> Graph.
Notation "gObj ** gLnk" := (graph gObj gLnk) (at level 64).
Definition Model := Graph.
Definition Fragment := Graph.


Inductive FragSubst :=
  fragsubst : Fragment -> Fragment -> LinkSet -> FragSubst.
Notation "p ,. r ., bdg" := (fragsubst p r bdg) (at level 65).
Definition FragSubstSet := list FragSubst.







Module OBJECT.

Module SET.

(*  Contains  *)
Inductive Contains : ObjectSet -> Object -> Prop :=
  | Contains_h : forall o t, Contains (o::t) o
  | Contains_t : forall o h t, Contains t o -> Contains (h::t) o.

Definition Contains_dec (s : ObjectSet) (o : Object) := 
  { Contains s o } + { ~Contains s o }.

Definition contains: forall s o, Contains_dec s o.
refine (fix contains s o: Contains_dec s o := 
  match s with
  | [] => right _
  | h::t => if eq_nat_dec h o
            then left _
            else if contains t o
                 then left _
                 else right _
  end).
Proof.
  unfold not. intro. inversion H.
  rewrite _H. apply Contains_h.
  apply Contains_t. apply _H0.
  unfold not. intro. inversion H. apply _H. apply H0.
    unfold not in _H0. apply _H0. apply H3.
Defined.

Definition bContains (s : ObjectSet) (o : Object) : bool :=
  if contains s o then true else false.

Lemma Contains_bProp : forall s o,
  (bContains s o) = true <-> Contains s o.
Proof.
  intros. split.
  unfold bContains. destruct (contains s o) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bContains. destruct (contains s o) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.

Lemma NotContains_bProp : forall s o,
  (bContains s o) = false <-> ~Contains s o.
Proof.
  intros. split.
  unfold bContains. destruct (contains s o) as [T | F].
    intro. inversion H.
    intro. auto.
  intro. unfold bContains. destruct (contains s o) as [T | F].
    contradiction.
    reflexivity.
Qed.





(* IsSet *)

Inductive IsSet : ObjectSet -> Prop :=
  | IsSet_nil  : IsSet []
  | IsSet_cons : forall s o, ~Contains s o /\ IsSet s -> IsSet (o::s).

Definition IsSet_dec (s : ObjectSet) :=
  { IsSet s } + { ~IsSet s }.

Definition isSet: forall s, IsSet_dec s.
refine (fix isSet s : IsSet_dec s :=
  match s with
  | [] => left _
  | h::t => if contains t h
            then right _
            else if isSet t
                 then left _
                 else right _
  end).
Proof.
  apply IsSet_nil.
  unfold not. intro. inversion H. inversion H1. unfold not in H3. apply H3. apply _H.
  apply IsSet_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H1. unfold not in _H0. apply _H0. apply H4.
Defined.

Definition bIsSet (s : ObjectSet) : bool :=
  if isSet s then true else false.

Lemma IsSet_bProp : forall s,
  (bIsSet s) = true <-> IsSet s.
Proof.
  intros. split.
  unfold bIsSet. destruct (isSet s) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bIsSet. destruct (isSet s) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.







(* Subset *)

Inductive Subset : ObjectSet -> ObjectSet -> Prop :=
  | Subset_nil  : forall s, Subset [] s
  | Subset_cons : forall h t s, Subset t s /\ Contains s h -> Subset (h::t) s.

Definition Subset_dec (s1 s2 : ObjectSet) :=
  { Subset s1 s2 } + { ~Subset s1 s2 }.

Definition subset: forall s1 s2, Subset_dec s1 s2.
refine (fix subset s1 s2 : Subset_dec s1 s2 :=
  match s1 with
  | [] => left _
  | h::t => if subset t s2
            then (if contains s2 h
                  then left _
                  else right _)
            else right _
  end).
Proof.
  apply Subset_nil.
  apply Subset_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H3. unfold not in _H0. apply _H0. apply H5.
  unfold not. intro. inversion H. inversion H3. unfold not in _H. apply _H. apply H4.
Defined.

Definition bSubset (s1 s2 : ObjectSet) : bool :=
  if subset s1 s2 then true else false.




Lemma Subset_consR : forall s t h,
  Subset s t -> Subset s (h::t).
Proof.
  intros. induction s as [|h' s'].
    constructor.
    constructor. split. apply IHs'. inversion_clear H. inversion_clear H0. auto.
    constructor. inversion_clear H. inversion_clear H0. auto.
Qed.

Lemma Subset_Contains_trans : forall h s1 s2,
  Contains s1 h /\ Subset s1 s2 -> Contains s2 h.
Proof.
  intros. induction s1 as [|h1' s1'].
    inversion_clear H. inversion_clear H0.
    inversion_clear H. inversion H0. inversion_clear H0. inversion_clear H1.
      inversion_clear H. rewrite <- H4. auto.
      apply IHs1'. split. auto. inversion_clear H1. inversion_clear H0. auto.
      apply IHs1'. inversion_clear H1. inversion_clear H5. auto.
Qed.


Lemma Subset_refl : forall s, Subset s s.
Proof.
  intro. induction s as [|h t].
    constructor.
    constructor. split. apply Subset_consR. auto. constructor.
Qed.

Lemma Subset_trans : forall s1 s2 s3,
  Subset s1 s2 /\ Subset s2 s3 -> Subset s1 s3.
Proof.
  intros. induction s1 as [|h1' s1'].
  constructor.
  inversion_clear H. inversion_clear H0. inversion_clear H. constructor. split.
    apply IHs1'. auto.
    apply Subset_Contains_trans with (s1 := s2). auto.
Qed.

Lemma SubsetRight : forall o s1 s2,
  Subset s1 s2 -> Subset s1 (o :: s2).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion_clear H0. auto. constructor. inversion_clear H.
  inversion_clear H0. auto.
Qed.


Lemma SubsetH : forall o s1 s2,
  Subset s1 s2 -> Subset (o::s1) (o::s2).
Proof.
  intros. induction s1 as [|h t].
  constructor. split. constructor. constructor.
  constructor. split. apply SubsetRight. auto. constructor.
Qed.






(* Equal *)

Inductive Equal : ObjectSet -> ObjectSet -> Prop :=
  | Equal_ : forall s1 s2, Subset s1 s2 /\ Subset s2 s1 -> Equal s1 s2.

Definition Equal_dec (s1 s2 : ObjectSet) :=
  { Equal s1 s2 } + { ~Equal s1 s2 }.

Definition equal: forall s1 s2, Equal_dec s1 s2.
refine (fix equal s1 s2 : Equal_dec s1 s2 :=
  if subset s1 s2
  then (if subset s2 s1
        then left _
        else right _)
  else right _
  ).
Proof.
  apply Equal_. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H0. unfold not in _H0. apply _H0. apply H4.
  unfold not. intro. inversion H. inversion H0. unfold not in _H. apply _H. apply H3.
Defined.

Definition bEqual (s1 s2 : ObjectSet) : bool :=
  if equal s1 s2 then true else false.


Lemma Equal_refl: forall s,
  Equal s s.
Proof.
  intro. constructor. split. apply Subset_refl. apply Subset_refl.
Qed.

Lemma Equal_sym : forall s1 s2,
  Equal s1 s2 -> Equal s2 s1.
Proof.
  intros. inversion_clear H. inversion_clear H0. constructor. auto.
Qed.

Lemma Equal_trans : forall s1 s2 s3,
  Equal s1 s2 /\ Equal s2 s3 -> Equal s1 s3.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split. apply Subset_trans with (s2 := s2). auto.
  apply Subset_trans with (s2 := s2). auto.
Qed.

Lemma EqualNil : forall s,
  Equal [] s -> s = [].
Proof.
  intros. inversion H. inversion H0. inversion H4. reflexivity. inversion H5. inversion H9.
Qed.


Lemma SubsetContainsSameObjects : forall o s1 s2,
  Subset s1 s2 /\ Contains s1 o -> Contains s2 o.
Proof.
  intros.
  induction s1 as [|h t]. inversion H. inversion H1.
  inversion_clear H. inversion H1. rewrite H4 in H0. inversion_clear H0. inversion_clear H.
  auto. apply IHt. split. inversion_clear H0. inversion_clear H5. auto. auto.
Qed.


Lemma EqualSetsContainSameObjects : forall o s1 s2,
  Equal s1 s2 /\ Contains s1 o -> Contains s2 o.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H.
  apply SubsetContainsSameObjects with (s1 := s1). split. auto. auto.
Qed.




Fixpoint union (s1 s2 : ObjectSet) : ObjectSet :=
match s1 with
  | []   => s2
  | h::t => if contains s2 h
            then union t s2
            else h::(union t s2)
end.

Theorem unionContains : forall o s1 s2,
  Contains s1 o \/ Contains s2 o -> Contains (union s1 s2) o.
Proof.
  intros. induction s1 as [|h t].
  (* s1 = [] *)
    simpl. inversion H. inversion H0. apply H0.
  (* s1 = h::t *)
    inversion_clear H.
    (* Contains (h :: t) o *)
      inversion H0.
      (* h = o *)
        simpl.
        destruct (contains s2 o).
        (* Contains s2 o *)
          apply IHt. right. auto.
        (* ~Contains s2 o *)
          apply Contains_h.
      (* Contains t o *)
        simpl.
        destruct (contains s2 h).
        (* Contains s2 h *)
          apply IHt. left. apply H3.
        (* ~ Contains s2 h *)
          constructor. apply IHt. left. auto.
    (* Contains s2 o *)
      simpl.
      destruct (contains s2 h).
      (* Contains s2 h *)
        apply IHt. right. auto.
      (* ~Contains s2 h *)
        constructor. apply IHt. right. auto.
Qed.






Theorem SubsetsUnionLeft : forall s1 s2 s3,
  Subset s1 s2 -> Subset s1 (union s2 s3).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion H0. apply H. apply unionContains. left. inversion_clear H.
  inversion_clear H0. auto.
Qed.

Theorem SubsetsUnionRight : forall s1 s2 s3,
  Subset s1 s2 -> Subset s1 (union s3 s2).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion H0. apply H. apply unionContains. right. inversion_clear H.
  inversion_clear H0. auto.
Qed.


Theorem UnionSubset : forall s1 s2 s,
  Subset s1 s /\ Subset s2 s -> Subset (union s1 s2) s.
Proof.
  intros. induction s1 as [|h1 t1]. simpl. inversion_clear H. auto.
  unfold union. fold union. destruct (contains s2 h1) as [T|F].
  apply IHt1. split. inversion_clear H. inversion_clear H0. inversion_clear H. auto.
  inversion_clear H. auto.
  constructor. split. apply IHt1. split. inversion_clear H. inversion_clear H0.
  inversion_clear H. auto. inversion_clear H. auto. inversion_clear H. inversion_clear H0.
  inversion_clear H. auto.
Qed.

Definition Consistent := Subset.




Lemma SubsetUnionOfObjectSubsets : forall o1 o1' o2 o2',
  Subset o1 o1' /\ Subset o2 o2' -> Subset (union o1 o2) (union o1' o2').
Proof.
  intros. inversion_clear H. induction o1 as [|h1 t1].
    simpl. apply SubsetsUnionRight. auto.
    inversion_clear H0. inversion_clear H. unfold union. fold union.
    destruct (contains o2 h1) as [T|F].
      apply IHt1. auto.
      constructor. split. apply IHt1. auto. apply unionContains. auto.
Qed.

Lemma EqualUnionOfEqualObjectSets : forall o1 o1' o2 o2',
  Equal o1 o1' /\ Equal o2 o2' -> Equal (union o1 o2) (union o1' o2').
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split.
    apply SubsetUnionOfObjectSubsets. auto.
    apply SubsetUnionOfObjectSubsets. auto.
Qed.


End SET.

End OBJECT.







Module LINK.


(* Equal *)

Inductive Equal : Link -> Link -> Prop :=
  | Equal_ : forall id1 src1 tgt1 id2 src2 tgt2,
           id1 = id2 /\ src1 = src2 /\ tgt1 = tgt2
           -> Equal (id1¤src1-->tgt1) (id2¤src2-->tgt2).

Definition Equal_dec (l1 l2 : Link) :=
  { Equal l1 l2 } + { ~Equal l1 l2 }.

Definition equal: forall l1 l2, Equal_dec l1 l2.
refine (fix equal l1 l2 : Equal_dec l1 l2 :=
  match l1, l2 with
    | (id1¤src1-->tgt1),
      (id2¤src2-->tgt2) => if eq_nat_dec id1 id2
                           then (if eq_nat_dec src1 src2
                                 then (if eq_nat_dec tgt1 tgt2
                                       then left _
                                       else right _)
                                 else right _)
                           else right _
  end).
Proof.
  apply Equal_. split. apply _H. split. apply _H0. apply _H1.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    contradiction.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    contradiction.
  unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bEqual (l1 l2 : Link) : bool :=
  if equal l1 l2 then true else false.

Lemma Equal_refl : forall l, Equal l l.
Proof.
  intro. destruct l as [id src tgt]. apply Equal_. split. reflexivity. split. reflexivity.
    reflexivity.
Qed.

Lemma Equal_sym : forall l1 l2,
  Equal l1 l2 -> Equal l2 l1.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H1.
  apply Equal_. split. symmetry. apply H. split. symmetry. apply H0. symmetry. apply H2.
Qed.

Lemma Equal_trans : forall l1 l2 l3,
  Equal l1 l2 /\ Equal l2 l3 -> Equal l1 l3.
Proof.
  intros. inversion_clear H. destruct l1 as [id1 src1 tgt1]. destruct l2 as [id2 src2 tgt2].
  destruct l3 as [id3 src3 tgt3]. inversion_clear H0. inversion_clear H1.
  inversion_clear H. inversion_clear H2. inversion_clear H0. inversion_clear H4.
  constructor. split. rewrite H1. rewrite H2. reflexivity. split. rewrite H. rewrite H0.
  reflexivity. rewrite H3. rewrite H5. reflexivity.
Qed.

Lemma Equal_eq : forall l1 l2,
  Equal l1 l2 <-> l1 = l2.
Proof.
  split.
  intro. inversion_clear H. inversion_clear H0. inversion_clear H1. rewrite H. rewrite H0.
    rewrite H2. reflexivity.
  intro. rewrite H. apply Equal_refl.
Qed. 




(* EqualId *)

Inductive EqualId : Link -> Link -> Prop :=
  | EqualId_ : forall id1 src1 tgt1 id2 src2 tgt2,
           id1 = id2 -> EqualId (id1¤src1-->tgt1) (id2¤src2-->tgt2).

Definition EqualId_dec (l1 l2 : Link) :=
  { EqualId l1 l2 } + { ~EqualId l1 l2 }.

Definition equalId: forall l1 l2, EqualId_dec l1 l2.
refine (fix equalId l1 l2 : EqualId_dec l1 l2 :=
  match l1, l2 with
    | (id1¤src1-->tgt1), (id2¤src2-->tgt2) => if eq_nat_dec id1 id2
                                              then left _
                                              else right _
  end).
Proof.
  apply EqualId_. apply _H.
  unfold not. intro. inversion_clear H. contradiction.
Defined.

Definition bEqualId (l1 l2 : Link) : bool :=
  if equalId l1 l2 then true else false.

Lemma EqualId_refl : forall l,
  EqualId l l.
Proof.
  intro. destruct l. constructor. reflexivity.
Qed.

Lemma EqualId_sym : forall l1 l2,
  EqualId l1 l2 -> EqualId l2 l1.
Proof.
  intros. inversion_clear H.
  apply EqualId_. symmetry. apply H0.
Qed.


Lemma EqualId_trans : forall l1 l2 l3,
  EqualId l1 l2 /\ EqualId l2 l3 -> EqualId l1 l3.
Proof.
  intros. inversion_clear H. destruct l1 as [id1 src1 tgt1].
  destruct l2 as [id2 src2 tgt2]. destruct l3 as [id3 src3 tgt3].
  inversion_clear H0. inversion_clear H1.
  constructor. rewrite H. rewrite H0. reflexivity.
Qed.




Module SET.

(*  Contains  *)

Inductive Contains : LinkSet -> Link -> Prop :=
  | Contains_h : forall l h t, LINK.Equal l h -> Contains (h::t) l
  | Contains_t : forall l h t, Contains t l -> Contains (h::t) l.

Definition Contains_dec (s : LinkSet) (l : Link) := 
  { Contains s l } + { ~Contains s l }.

Definition contains: forall s l, Contains_dec s l.
refine (fix contains s l: Contains_dec s l := 
  match s with
  | [] => right _
  | h::t => if LINK.equal h l
            then left _
            else if contains t l
                 then left _
                 else right _
  end).
Proof.
  unfold not. intro. inversion H.
  apply Contains_h. apply LINK.Equal_sym. apply _H.
  apply Contains_t. apply _H0.
  unfold not. intro. inversion_clear H. apply LINK.Equal_sym in H0. contradiction.
    contradiction.
Defined.

Definition bContains (s : LinkSet) (l : Link) : bool :=
  if contains s l then true else false.

Lemma Contains_bProp : forall s l,
  (bContains s l) = true <-> Contains s l.
Proof.
  intros. split.
  unfold bContains. destruct (contains s l) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bContains. destruct (contains s l) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.

Lemma NotContains_bProp : forall s l,
  (bContains s l) = false <-> ~Contains s l.
Proof.
  intros. split.
  unfold bContains. destruct (contains s l) as [T | F].
    intro. inversion H.
    intro. auto.
  intro. unfold bContains. destruct (contains s l) as [T | F].
    contradiction.
    reflexivity.
Qed.



(*  ContainsId  *)

Inductive ContainsId : LinkSet -> Link -> Prop :=
  | ContainsId_h : forall l h t, LINK.EqualId l h -> ContainsId (h::t) l
  | ContainsId_t : forall l h t, ContainsId t l -> ContainsId (h::t) l.

Definition ContainsId_dec (s : LinkSet) (l : Link) := 
  { ContainsId s l } + { ~ContainsId s l }.

Definition containsId: forall s l, ContainsId_dec s l.
refine (fix containsId s l: ContainsId_dec s l := 
  match s with
  | [] => right _
  | h::t => if LINK.equalId h l
            then left _
            else if containsId t l
                 then left _
                 else right _
  end).
Proof.
  unfold not. intro. inversion H.
  apply ContainsId_h. apply LINK.EqualId_sym. apply _H.
  apply ContainsId_t. apply _H0.
  unfold not. intro. inversion_clear H. apply LINK.EqualId_sym in H0. contradiction.
    contradiction.
Defined.

Definition bContainsId (s : LinkSet) (l : Link) : bool :=
  if containsId s l then true else false.

Lemma ContainsId_bProp : forall s l,
  (bContainsId s l) = true <-> ContainsId s l.
Proof.
  intros. split.
  unfold bContainsId. destruct (containsId s l) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bContainsId. destruct (containsId s l) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.

Lemma NotContainsId_bProp : forall s l,
  (bContainsId s l) = false <-> ~ContainsId s l.
Proof.
  intros. split.
  unfold bContainsId. destruct (containsId s l) as [T | F].
    intro. inversion H.
    intro. auto.
  intro. unfold bContainsId. destruct (containsId s l) as [T | F].
    contradiction.
    reflexivity.
Qed.



Theorem ContainsImpliesContainsId : forall l s,
  Contains s l -> ContainsId s l.
Proof.
  intros. destruct l as [id src tgt]. induction s as [|h t].
  inversion H.
  inversion_clear H. inversion_clear H0. inversion_clear H. rewrite H0. apply ContainsId_h.
    apply EqualId_. reflexivity.
  apply ContainsId_t. apply IHt. apply H0.
Qed.





(* IsSet *)

Inductive IsSet : LinkSet -> Prop :=
  | IsSet_nil  : IsSet []
  | IsSet_cons : forall s l, ~ContainsId s l /\ IsSet s -> IsSet (l::s).

Definition IsSet_dec (s : LinkSet) :=
  { IsSet s } + { ~IsSet s }.

Definition isSet: forall s, IsSet_dec s.
refine (fix isSet s : IsSet_dec s :=
  match s with
  | [] => left _  
  | h::t => if containsId t h
            then right _
            else if isSet t
                 then left _
                 else right _
  end).
Proof.
  apply IsSet_nil.
  unfold not. intro. inversion H. inversion H1. unfold not in H3. apply H3. apply _H.
  apply IsSet_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H1. unfold not in _H0. apply _H0. apply H4.
Defined.

Definition bIsSet (s : LinkSet) : bool :=
  if isSet s then true else false.



(* Subset *)

Inductive Subset : LinkSet -> LinkSet -> Prop :=
  | Subset_nil  : forall s, Subset [] s
  | Subset_cons : forall h t s, Subset t s /\ ContainsId s h -> Subset (h::t) s.

Definition Subset_dec (s1 s2 : LinkSet) :=
  { Subset s1 s2 } + { ~Subset s1 s2 }.

Definition subset: forall s1 s2, Subset_dec s1 s2.
refine (fix subset s1 s2 : Subset_dec s1 s2 :=
  match s1 with
  | [] => left _
  | h::t => if subset t s2
            then (if containsId s2 h
                  then left _
                  else right _)
            else right _
  end).
Proof.
  apply Subset_nil.
  apply Subset_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H3. unfold not in _H0. apply _H0. apply H5.
  unfold not. intro. inversion H. inversion H3. unfold not in _H. apply _H. apply H4.
Defined.


Definition bSubset (s1 s2 : LinkSet) : bool :=
  if subset s1 s2 then true else false.



Eval compute in bSubset [] [].
Eval compute in bSubset [1¤1-->2] [].
Eval compute in bSubset [] [1¤1-->2].
Eval compute in bSubset [1¤1-->2] [1¤1-->2].
Eval compute in bSubset [1¤1-->2] [1¤3-->2].
Eval compute in bSubset [1¤1-->2] [1¤1-->3].
Eval compute in bSubset [1¤1-->2] [3¤3-->2; 1¤1-->2].
Eval compute in bSubset [1¤1-->2] [1¤1-->2; 4¤1-->3].


Lemma Subset_consR : forall s t h,
  Subset s t -> Subset s (h::t).
Proof.
  intros. induction s as [|h' s'].
    constructor.
    constructor. split. apply IHs'. inversion_clear H. inversion_clear H0. auto.
    apply ContainsId_t. inversion_clear H. inversion_clear H0. auto.
Qed.

Lemma ContainsEqualIds : forall l1 l2 s,
  EqualId l1 l2 /\ ContainsId s l1 -> ContainsId s l2.
Proof.
  intros. induction s as [|h t].
  inversion_clear H. inversion_clear H1.
  inversion_clear H. destruct l1 as [id1 src1 tgt1]. destruct l2 as [id2 src2 tgt2].
  destruct h as [idh srch tgth]. inversion_clear H0. inversion_clear H1.
  inversion_clear H0. constructor. rewrite <- H. rewrite <- H1. constructor. reflexivity.
  apply ContainsId_t. apply IHt. split. rewrite H. constructor. reflexivity. auto.
Qed.

Lemma Subset_Contains_trans : forall h s1 s2,
  ContainsId s1 h /\ Subset s1 s2 -> ContainsId s2 h.
Proof.
  intros. induction s1 as [|h1' s1'].
    inversion_clear H. inversion_clear H0.
    inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H0.
    apply ContainsEqualIds with (l1 := h1'). apply EqualId_sym in H. auto.
    apply IHs1'. inversion_clear H1. inversion_clear H0. auto.
Qed.

Lemma Subset_refl : forall s, Subset s s.
Proof.
  intro. induction s as [|h t].
    constructor.
    constructor. split. apply Subset_consR. auto. constructor. apply EqualId_refl.
Qed.

Lemma Subset_trans : forall s1 s2 s3,
  Subset s1 s2 /\ Subset s2 s3 -> Subset s1 s3.
Proof.
  intros. induction s1 as [|h1' s1'].
  constructor.
  inversion_clear H. inversion_clear H0. inversion_clear H. constructor. split.
    apply IHs1'. auto.
    apply Subset_Contains_trans with (s1 := s2). auto.
Qed.







(* Equal *)

Inductive Equal : LinkSet -> LinkSet -> Prop :=
  | Equal_ : forall s1 s2, Subset s1 s2 /\ Subset s2 s1 -> Equal s1 s2.

Definition Equal_dec (s1 s2 : LinkSet) :=
  { Equal s1 s2 } + { ~Equal s1 s2 }.

Definition equal: forall s1 s2, Equal_dec s1 s2.
refine (fix equal s1 s2 : Equal_dec s1 s2 :=
  if subset s1 s2
  then (if subset s2 s1
        then left _
        else right _)
  else right _
  ).
Proof.
  apply Equal_. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H0. unfold not in _H0. apply _H0. apply H4.
  unfold not. intro. inversion H. inversion H0. unfold not in _H. apply _H. apply H3.
Defined.

Definition bEqual (s1 s2 : LinkSet) : bool :=
  if equal s1 s2 then true else false.


Lemma Equal_refl: forall s,
  Equal s s.
Proof.
  intro. constructor. split. apply Subset_refl. apply Subset_refl.
Qed.

Lemma Equal_sym : forall s1 s2,
  Equal s1 s2 -> Equal s2 s1.
Proof.
  intros. inversion_clear H. inversion_clear H0. constructor. auto.
Qed.

Lemma Equal_trans : forall s1 s2 s3,
  Equal s1 s2 /\ Equal s2 s3 -> Equal s1 s3.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split. apply Subset_trans with (s2 := s2). auto.
  apply Subset_trans with (s2 := s2). auto.
Qed.










Fixpoint union (s1 s2 : LinkSet) : LinkSet :=
match s1 with
  | []   => s2
  | h::t => if containsId s2 h
            then union t s2
            else h::(union t s2)
end.


Theorem setContainsLinksWithSameId : forall l1 l2 s,
  EqualId l1 l2 /\ ContainsId s l1 -> ContainsId s l2.
Proof.
  intros. induction s as [|h t].
  (* s = [] *)
    inversion H. inversion H1.
  (* s = h::t *)
    inversion_clear H. inversion_clear H1.
    (* EqualId l1 h *)
      apply ContainsId_h. destruct l1 as [id1 src1 tgt1].
      destruct l2 as [id2 src2 tgt2]. destruct h as [idh srch tgth]. inversion_clear H0.
      inversion_clear H. apply EqualId_. rewrite <- H0. rewrite H1. reflexivity.
    (* ContainsId t l1 *)
      apply ContainsId_t. apply IHt. split. apply H0. apply H.
Qed.

Theorem unionContains : forall l s1 s2,
  ContainsId s1 l \/ ContainsId s2 l <-> ContainsId (union s1 s2) l.
Proof.
  intros. split.
  (* left *)
  intros. induction s1 as [|h t].
  (* s1 = [] *)
    simpl. inversion H. inversion H0. apply H0.
  (* s1 = h::t *)
    inversion_clear H.
    (* Contains (h :: t) l *)
      inversion_clear H0.
      (* EqualId l h *)
        simpl.
        destruct (containsId s2 h).
        (* ContainsId s2 h *)
          apply IHt. right.
          apply setContainsLinksWithSameId with (l1 := h) (l2 := l) (s := s2).
          split. apply EqualId_sym. apply H. auto.
        (* ~ContainsId s2 h *)
          apply ContainsId_h. apply H.
      (* ContainsId t l *)
        simpl.
        destruct (containsId s2 h).
        (* ContainsId s2 h *)
          apply IHt. left. apply H.
        (* ~ContainsId s2 h *)
          apply ContainsId_t. apply IHt. left. apply H.
    (* ContainsId s2 l *)
      simpl.
      destruct (containsId s2 h).
      (* ContainsId s2 h *)
        apply IHt. right. auto.
      (* ~ContainsId s2 h *)
        apply ContainsId_t. apply IHt. right. auto.
  (* right *)
    intro.
    induction s1 as [|h t].
    simpl in H. right. auto.
    simpl in H. destruct (containsId s2 h).
      apply IHt in H. inversion_clear H. left. constructor 2. auto. right. auto.
      inversion_clear H. left. constructor. auto. apply IHt in H0. inversion_clear H0.
      left. constructor 2. auto. right. auto.
Qed.



Theorem unionDoesNotContain : forall l s1 s2,
  ~ContainsId s1 l /\ ~ContainsId s2 l -> ~ContainsId (union s1 s2) l.
Proof.
  intros. induction s1 as [|h t].
  - simpl. inversion H. apply H1.
  - inversion_clear H. simpl. destruct (containsId s2 h).
    + apply IHt. split.
      * unfold not in H0. unfold not. intro. apply H0. apply ContainsId_t. apply H.
      * apply H1.
    + unfold not. intro. inversion H.
      * unfold not in H0. apply H0. apply ContainsId_h. auto.
      * generalize dependent H5. apply IHt. { split.
        - unfold not. intro. unfold not in H0. apply H0. apply ContainsId_t. auto.
        - auto. }
Qed.


Theorem unionProducesSet : forall s1 s2,
  IsSet s1 /\ IsSet s2 -> IsSet (union s1 s2).
Proof.
  intros. induction s1 as [|h t].
  (* s1 = [] *)
    simpl. inversion H. apply H1.
  (* s1 = h::t *)
    simpl. destruct (containsId s2 h).
    (* ContainsId s2 h *)
      apply IHt. inversion_clear H. inversion_clear H0. inversion_clear H. split. auto. auto.
    (* ~ContainsId s2 h *)
      apply IsSet_cons. split.
      (* ~ ContainsId (union t s2) h *)
        apply unionDoesNotContain. split. inversion_clear H. inversion_clear H0.
        inversion_clear H. apply H0. apply n.
      (* IsSet (union t s2) *)
        apply IHt. inversion_clear H. inversion_clear H0. inversion_clear H. split. auto.
        auto.
Qed.



Theorem SubsetsUnionLeft : forall s1 s2 s3,
  Subset s1 s2 -> Subset s1 (union s2 s3).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion H0. apply H. apply unionContains. left. inversion_clear H.
  inversion_clear H0. auto.
Qed.

Theorem SubsetsUnionRight : forall s1 s2 s3,
  Subset s1 s2 -> Subset s1 (union s3 s2).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion H0. apply H. apply unionContains. right. inversion_clear H.
  inversion_clear H0. auto.
Qed.


Theorem UnionSubset : forall s1 s2 s,
  Subset s1 s /\ Subset s2 s -> Subset (union s1 s2) s.
Proof.
  intros. induction s1 as [|h1 t1]. simpl. inversion_clear H. auto.
  unfold union. fold union. destruct (containsId s2 h1) as [T|F].
  apply IHt1. split. inversion_clear H. inversion_clear H0. inversion_clear H. auto.
  inversion_clear H. auto.
  constructor. split. apply IHt1. split. inversion_clear H. inversion_clear H0.
  inversion_clear H. auto. inversion_clear H. auto. inversion_clear H. inversion_clear H0.
  inversion_clear H. auto.
Qed.


Lemma ContainsIdForInconsistentLinks : forall s id src1 tgt1 src2 tgt2,
  ContainsId s (id¤src1-->tgt1) -> ContainsId s (id¤src2-->tgt2).
Proof.
  intros. induction s as [|h t]. inversion H.
  destruct h as [idh srch tgth]. inversion_clear H. inversion_clear H0.
  constructor. constructor. auto. apply ContainsId_t. apply IHt. auto.
Qed.



Lemma SubsetsContainSameLinks : forall l s1 s2,
  Subset s1 s2 /\ ContainsId s1 l -> ContainsId s2 l.
Proof.
  intros.
  induction s1 as [|h t]. inversion H. inversion H1.
  inversion_clear H. inversion H1. destruct h as [idh srch tgth].
  destruct l as [idl srcl tgtl]. inversion_clear H4. rewrite <- H5 in H0. inversion_clear H0.
  inversion_clear H4.
  apply ContainsIdForInconsistentLinks with (src1 := srch) (tgt1 := tgth). auto.
  apply IHt. split. inversion_clear H0. inversion_clear H5. auto. auto.
Qed.




Lemma EqualSetsContainSameLinks : forall l s1 s2,
  Equal s1 s2 /\ ContainsId s1 l -> ContainsId s2 l.
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H.
  apply SubsetsContainSameLinks with (s1 := s1). split. auto. auto.
Qed.



Lemma SubsetRight : forall l s1 s2,
  Subset s1 s2 -> Subset s1 (l :: s2).
Proof.
  intros. induction s1 as [|h t]. constructor. constructor. split. apply IHt.
  inversion_clear H. inversion_clear H0. auto. inversion_clear H. inversion_clear H0.
  apply ContainsId_t. auto.
Qed.


Lemma SubsetH : forall l s1 s2,
  Subset s1 s2 -> Subset (l::s1) (l::s2).
Proof.
  intros. induction s1 as [|h t].
  constructor. split. constructor. constructor. destruct l. constructor. reflexivity.
  constructor. split. apply SubsetRight. auto. constructor.
  destruct l. constructor. reflexivity.
Qed.













(* Consistent *) 

Inductive Consistent : LinkSet -> LinkSet -> Prop :=
  | Consistent_nil  : forall s, IsSet s -> Consistent [] s
  | Consistent_cons : forall h t s, IsSet (h::t) /\ IsSet s /\ Consistent t s
                       /\ Contains s h -> Consistent (h::t) s.

Definition Consistent_dec (s1 s2 : LinkSet) :=
  { Consistent s1 s2 } + { ~Consistent s1 s2 }.

Definition consistent: forall s1 s2, Consistent_dec s1 s2.
refine (fix consistent s1 s2 : Consistent_dec s1 s2 :=
  match s1 with
  | [] => if isSet s2
          then left _
          else right _
  | h::t => if isSet (h::t)
            then (if isSet s2
                 then (if consistent t s2
                       then (if contains s2 h
                             then left _
                             else right _)
                       else right _ )
                 else right _)
            else right _
  end).
Proof.
  (* 1/7 *) constructor. auto.
  (* 2/7 *) unfold not. intro. inversion H. contradiction.
  (* 3/7 *) constructor. split. auto. split. auto. split. auto. auto.
  (* 4/7 *) unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    inversion_clear H2. contradiction.
  (* 5/7 *) unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    inversion_clear H2. contradiction.
  (* 6/7 *) unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    contradiction.
  (* 7/7 *) unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bConsistent (s1 s2 : LinkSet) : bool :=
  if consistent s1 s2 then true else false.

Eval compute in bConsistent [] [].
Eval compute in bConsistent [1¤1-->2] [].
Eval compute in bConsistent [] [1¤1-->2].
Eval compute in bConsistent [1¤1-->2] [1¤1-->2].
Eval compute in bConsistent [1¤1-->2] [1¤3-->2].
Eval compute in bConsistent [1¤1-->2] [1¤1-->3].
Eval compute in bConsistent [1¤1-->2] [3¤3-->2].
Eval compute in bConsistent [1¤1-->2] [4¤1-->3].









(* IsClosed *)

Inductive IsClosed : LinkSet -> ObjectSet -> Prop :=
  | IsClosed_nil  : forall Obj, IsClosed [] Obj
  | IsClosed_cons : forall id src tgt t Obj,
                  IsClosed t Obj /\ OBJECT.SET.Contains Obj src /\
                  OBJECT.SET.Contains Obj tgt -> IsClosed ((id¤src-->tgt)::t) Obj.

Definition IsClosed_dec (Lnk : LinkSet) (Obj : ObjectSet) :=
  { IsClosed Lnk Obj } + { ~IsClosed Lnk Obj }.

Definition isClosed: forall Lnk Obj, IsClosed_dec Lnk Obj.
refine (fix isClosed Lnk Obj : IsClosed_dec Lnk Obj :=
  match Lnk with
  | [] => left _
  | (id¤src-->tgt)::t => if isClosed t Obj
                         then (if OBJECT.SET.contains Obj src
                               then (if OBJECT.SET.contains Obj tgt
                                     then left _
                                     else right _)
                               else right _)
                         else right _
  end).
Proof.
  - apply IsClosed_nil.
  - apply IsClosed_cons. split. auto. split. auto. auto.
  -  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
      contradiction.
  -  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
      contradiction.
  - unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bIsClosed (Lnk : LinkSet) (Obj : ObjectSet) : bool :=
  if isClosed Lnk Obj then true else false.




Lemma SubsetUnionOfLinkSubsets : forall l1 l1' l2 l2',
  Subset l1 l1' /\ Subset l2 l2'
  -> Subset (union l1 l2) (union l1' l2').
Proof.
  intros. inversion_clear H. induction l1 as [|h1 t1].
    simpl. apply SubsetsUnionRight. auto.
    inversion_clear H0. inversion_clear H. unfold union. fold union.
    destruct (containsId l2 h1) as [T|F].
      apply IHt1. auto.
      constructor. split. apply IHt1. auto. apply unionContains. auto.
Qed.

Lemma EqualUnionOfEqualLinkSets : forall l1 l1' l2 l2',
  Equal l1 l1' /\ Equal l2 l2' -> Equal (union l1 l2) (union l1' l2').
Proof.
  intros. inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split.
    apply SubsetUnionOfLinkSubsets. auto.
    apply SubsetUnionOfLinkSubsets. auto.
Qed.


Lemma ContainsIdImpliesContainsAny : forall id src1 src2 tgt1 tgt2 s,
  ContainsId s (id¤src1-->tgt1) -> ContainsId s (id¤src2-->tgt2).
Proof.
  intros. induction s as [|h t].
  inversion H.
  destruct h as [idh srch tgth]. inversion_clear H.
    constructor. constructor. inversion_clear H0. auto.
    apply ContainsId_t. apply IHt. auto.
Qed.


Lemma EqualIdsInSetImpliedEqualLinks : forall l1 l2 s,
  EqualId l1 l2 /\ IsSet s /\ Contains s l1 /\ Contains s l2 -> LINK.Equal l1 l2.
Proof.
  intros. inversion_clear H. inversion_clear H1. inversion_clear H2.
  induction s as [|h t].
    inversion H1.
    inversion_clear H1.
    (* LINK.Equal l1 h *)
      inversion_clear H3.
      (* LINK.Equal l2 h *)
        apply LINK.Equal_sym in H1. apply LINK.Equal_trans with (l2 := h). auto.
      (* LINK.SET.Contains t l2 *)
        destruct l1 as [id1 src1 tgt1]. destruct l2 as [id2 src2 tgt2].
        destruct h as [idh srch tgth]. inversion_clear H.
        apply LINK.SET.ContainsImpliesContainsId in H1. inversion_clear H3.
        inversion_clear H0. rewrite <- H3 in H1. inversion_clear H2.
        inversion_clear H0. rewrite H2 in H1.
        assert (H6 : LINK.SET.ContainsId t (idh ¤ srch --> tgth)).
        apply ContainsIdImpliesContainsAny with (src1 := src2) (tgt1 := tgt2). auto.
        contradiction.
    (* LINK.SET.Contains t l1 *)
      inversion_clear H3.
      (* LINK.Equal l2 h *)
        destruct l1 as [id1 src1 tgt1]. destruct l2 as [id2 src2 tgt2].
        destruct h as [idh srch tgth]. inversion_clear H.
        apply LINK.SET.ContainsImpliesContainsId in H2. inversion_clear H3.
        inversion_clear H0. rewrite H3 in H2. inversion_clear H1.
        inversion_clear H0. rewrite H1 in H2.
        assert (H6 : LINK.SET.ContainsId t (idh ¤ srch --> tgth)).
        apply ContainsIdImpliesContainsAny with (src1 := src1) (tgt1 := tgt1). auto.
        contradiction.
      (* LINK.SET.Contains t l2 *)
      apply IHt. inversion_clear H. inversion_clear H3. auto. auto. auto.
Qed.



Lemma ExtractConsistentLink : forall l rLnk mLnk,
  LINK.SET.ContainsId rLnk l /\ LINK.SET.Contains mLnk l /\ LINK.SET.Consistent rLnk mLnk
  -> LINK.SET.Contains rLnk l.
Proof.
  intros. inversion_clear H. inversion_clear H1. induction rLnk as [|h rLnk'].
  inversion H0. inversion_clear H0. constructor. inversion_clear H2.
  apply EqualIdsInSetImpliedEqualLinks with (s := mLnk). inversion_clear H0.
  inversion_clear H3. inversion_clear H4. auto.
  apply LINK.SET.Contains_t. apply IHrLnk'. auto. inversion_clear H2. inversion_clear H0.
  inversion_clear H3. inversion_clear H4. auto.
Qed.




Theorem ConsistentUnion : forall Lnk1 Lnk2 s,
  LINK.SET.Consistent Lnk1 s /\ LINK.SET.Consistent Lnk2 s
  -> LINK.SET.Consistent (LINK.SET.union Lnk1 Lnk2) s.
Proof.
  intros. induction Lnk1 as [|h t].
  simpl. inversion_clear H. auto.
  simpl. destruct (LINK.SET.containsId Lnk2 h).
    apply IHt. inversion_clear H. inversion_clear H0. inversion_clear H.
      inversion_clear H2. inversion_clear H3. auto.
    constructor. split. constructor. split. unfold not. intro. unfold not in n. apply n.
      apply LINK.SET.unionContains in H0. inversion_clear H0.
        inversion_clear H. inversion_clear H0. inversion_clear H. inversion_clear H0.
        inversion_clear H. contradiction. auto.
      apply LINK.SET.unionProducesSet. inversion_clear H. inversion_clear H0.
        inversion_clear H. inversion_clear H0. inversion_clear H. split. auto.
        destruct Lnk2 as [|h2 t2]. constructor. inversion_clear H1. inversion_clear H.
        auto.
      split. inversion_clear H. inversion_clear H0. inversion_clear H.
        inversion_clear H2. auto.
      split. apply IHt. inversion_clear H. inversion_clear H0. inversion_clear H.
        inversion_clear H2. inversion_clear H3. auto.
      inversion_clear H. inversion_clear H0. inversion_clear H. inversion_clear H2.
        inversion_clear H3. auto.
Qed.


End SET.
End LINK.









Module GRAPH.

(* Equal *)

Inductive Equal : Graph -> Graph -> Prop :=
  | Equal_ : forall o1 l1 o2 l2,
           OBJECT.SET.Equal o1 o2 /\ LINK.SET.Equal l1 l2 -> Equal (o1**l1) (o2**l2).

Definition Equal_dec (g1 g2 : Graph) :=
  { Equal g1 g2 } + { ~Equal g1 g2 }.

Definition equal: forall g1 g2, Equal_dec g1 g2.
refine (fix equal g1 g2 : Equal_dec g1 g2 :=
  match g1, g2 with
    | (o1**l1), (o2**l2) => if OBJECT.SET.equal o1 o2
                            then (if LINK.SET.equal l1 l2
                                  then left _
                                  else right _)
                            else right _
  end).
Proof.
  apply Equal_. split. apply _H. apply _H0.
  unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
  unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bEqual (g1 g2 : Graph) : bool :=
  if equal g1 g2 then true else false.



Lemma NilEqual :
  GRAPH.Equal ([]**[]) ([]**[]).
Proof.
  constructor. split. constructor. split. constructor. constructor. constructor. split.
  constructor. constructor.
Qed.

Lemma Equal_refl : forall g,
  Equal g g.
Proof.
  destruct g. constructor. split. apply OBJECT.SET.Equal_refl. apply LINK.SET.Equal_refl.
Qed.

Lemma Equal_sym : forall g1 g2,
  Equal g1 g2 -> Equal g2 g1.
Proof.
  intros. destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. inversion_clear H.
  inversion_clear H0. constructor. apply OBJECT.SET.Equal_sym in H.
  apply LINK.SET.Equal_sym in H1. auto.
Qed.

Lemma Equal_trans : forall g1 g2 g3,
  Equal g1 g2 /\ Equal g2 g3 -> Equal g1 g3.
Proof.
  intros. destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. destruct g3 as [o3 l3].
  inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split. apply OBJECT.SET.Equal_trans with (s2 := o2).
  auto. apply LINK.SET.Equal_trans with (s2 := l2). auto.
Qed.


Inductive IsClosed : Graph -> Prop :=
  IsClosed_ : forall Lnk Obj, LINK.SET.IsClosed Lnk Obj -> IsClosed (Obj**Lnk).

Definition IsClosed_dec (g : Graph) :=
  { IsClosed g } + { ~IsClosed g }.

Definition isClosed: forall g, IsClosed_dec g.
refine (fix isClosed g : IsClosed_dec g :=
  match g with
    | Obj**Lnk => if LINK.SET.isClosed Lnk Obj
                  then left _
                  else right _
  end).
Proof.
  - apply IsClosed_. apply _H.
  - unfold not. intro. inversion H. contradiction.
Defined.

Definition bIsClosed (g : Graph) : bool :=
  if isClosed g then true else false.






Inductive Subgraph : Graph -> Graph -> Prop :=
  | Subgraph_ : forall g1Obj g1Lnk g2Obj g2Lnk,
              OBJECT.SET.Subset g1Obj g2Obj /\ LINK.SET.Subset g1Lnk g2Lnk
              -> Subgraph (g1Obj**g1Lnk) (g2Obj**g2Lnk).

Definition Subgraph_dec (g1 g2 : Graph) :=
  { Subgraph g1 g2 } + { ~Subgraph g1 g2 }.

Definition subgraph: forall g1 g2, Subgraph_dec g1 g2.
refine (fix subgraph g1 g2 : Subgraph_dec g1 g2 :=
  match g1, g2 with
    | (g1Obj**g1Lnk), (g2Obj**g2Lnk) =>
                  if OBJECT.SET.subset g1Obj g2Obj
                  then (if LINK.SET.subset g1Lnk g2Lnk
                        then left _
                        else right _)
                  else right _
  end).
Proof.
  - apply Subgraph_. split. apply _H. apply _H0.
  - unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
  - unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bSubgraph (g1 g2 : Graph) : bool :=
  if subgraph g1 g2 then true else false.



Theorem subgraphsEqual : forall g1 g2,
  Subgraph g1 g2 /\ Subgraph g2 g1 <-> Equal g1 g2.
Proof.
  intros. destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. split.
  intro. inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
    inversion_clear H0. constructor. split. constructor. split. auto. auto. constructor.
    split. auto. auto.
  intro. inversion_clear H. inversion_clear H0. inversion_clear H. inversion_clear H1.
    inversion_clear H0. inversion_clear H. split. constructor. auto. constructor. auto.
Qed.




Definition union (g1 g2 : Graph) : Graph :=
match g1, g2 with
  g1Obj**g1Lnk, g2Obj**g2Lnk => (OBJECT.SET.union g1Obj g2Obj)**(LINK.SET.union g1Lnk g2Lnk)
end.


Theorem SplitSubgraph : forall g1 g2 g3,
  GRAPH.Subgraph g1 g2 \/ GRAPH.Subgraph g1 g3 -> GRAPH.Subgraph g1 (GRAPH.union g2 g3).
Proof.
  intros. destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. destruct g3 as [o3 l3].
  inversion_clear H. inversion_clear H0. inversion_clear H.
  constructor. split. apply OBJECT.SET.SubsetsUnionLeft. auto.
    apply LINK.SET.SubsetsUnionLeft. auto.
  inversion_clear H0. inversion_clear H. constructor. split.
    apply OBJECT.SET.SubsetsUnionRight. auto.
    apply LINK.SET.SubsetsUnionRight. auto.
Qed.


Lemma EqualUnionsOfEqualGraphs : forall g1 g1' g2 g2',
  Equal g1 g1' /\ Equal g2 g2' -> Equal (union g1 g2) (union g1' g2').
Proof.
  intros. destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. destruct g1' as [o1' l1'].
  destruct g2' as [o2' l2']. inversion_clear H. inversion_clear H0. inversion_clear H1.
  inversion_clear H. inversion_clear H0. simpl. constructor. split.
  apply OBJECT.SET.EqualUnionOfEqualObjectSets. auto.
  apply LINK.SET.EqualUnionOfEqualLinkSets. auto.
Qed.

Theorem GraphEqualSquare : forall g1 g1' g2 g2',
  Equal g1 g1' /\ Equal g2 g2' -> (Equal g1 g2 -> Equal g1' g2').
Proof.
  intros. inversion_clear H. destruct g1 as [o1 l1]. destruct g2 as [o2 l2].
  destruct g1' as [o1' l1']. destruct g2' as [o2' l2']. constructor.
  inversion_clear H0. inversion_clear H1. inversion_clear H2. inversion_clear H.
  inversion_clear H0. inversion_clear H1. split.
    apply OBJECT.SET.Equal_sym in H. assert (H6 : OBJECT.SET.Equal o1' o2).
    apply OBJECT.SET.Equal_trans with (s2 := o1). auto.
    apply OBJECT.SET.Equal_trans with (s2 := o2). auto.

    apply LINK.SET.Equal_sym in H4. assert (H6 : LINK.SET.Equal l1' l2).
    apply LINK.SET.Equal_trans with (s2 := l1). auto.
    apply LINK.SET.Equal_trans with (s2 := l2). auto.
Qed.

Theorem unionSubgraph : forall g1 g2 g3,
  Subgraph g1 g3 /\ Subgraph g2 g3 -> Subgraph (union g1 g2) g3.
Proof.
  destruct g1 as [o1 l1]. destruct g2 as [o2 l2]. destruct g3 as [o3 l3]. intros.
  inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H.
  inversion_clear H0. constructor. split.
    unfold OBJECT.SET.union. fold OBJECT.SET.union. apply OBJECT.SET.UnionSubset. split.
      auto. auto.
    unfold LINK.SET.union. fold LINK.SET.union. apply LINK.SET.UnionSubset. split. auto.
      auto.
Qed. 




Inductive Consistent : Graph -> Graph -> Prop :=
  | Consistent_ : forall g1Obj g1Lnk g2Obj g2Lnk,
                OBJECT.SET.Consistent g1Obj g2Obj /\ LINK.SET.Consistent g1Lnk g2Lnk
                -> Consistent (g1Obj**g1Lnk) (g2Obj**g2Lnk).

Definition Consistent_dec (g1 g2 : Graph) :=
  { Consistent g1 g2 } + { ~Consistent g1 g2 }.

Definition consistent: forall g1 g2, Consistent_dec g1 g2.
refine (fix consistent g1 g2 : Consistent_dec g1 g2 :=
  match g1, g2 with
  | g1Obj**g1Lnk, g2Obj**g2Lnk => if OBJECT.SET.subset g1Obj g2Obj
                                  then if LINK.SET.consistent g1Lnk g2Lnk
                                       then left _
                                       else right _
                                  else right _
  end).
Proof.
  (* 1/3 *) constructor. split. auto. auto.
  (* 2/3 *) unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
  (* 3/3 *) unfold not. intro. inversion_clear H. inversion_clear H0. contradiction.
Defined.

Definition bConsistent (g1 g2 : Graph) : bool :=
  if consistent g1 g2 then true else false.

End GRAPH.
Module MODEL := GRAPH.
Module FRAGMENT := GRAPH.






Module FS.

(* Equal *)

Inductive Equal : FragSubst -> FragSubst -> Prop :=
  | Equal_ : forall p1 r1 b1 p2 r2 b2,
              GRAPH.Equal p1 p2
           /\ GRAPH.Equal r1 r2
           /\ LINK.SET.Equal b1 b2
           -> Equal (p1,.r1.,b1) (p2,.r2.,b2).

Definition Equal_dec (fs1 fs2 : FragSubst) :=
  { Equal fs1 fs2 } + { ~Equal fs1 fs2 }.

Definition equal: forall fs1 fs2, Equal_dec fs1 fs2.
refine (fix equal fs1 fs2 : Equal_dec fs1 fs2 :=
  match fs1, fs2 with
    | (p1,.r1.,b1), (p2,.r2.,b2) => if GRAPH.equal p1 p2
                                    then (if GRAPH.equal r1 r2
                                          then (if LINK.SET.equal b1 b2
                                                then left _
                                                else right _)
                                          else right _)
                                    else right _
  end).
Proof.
  apply Equal_. split. apply _H. split. apply _H0. apply _H1.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    unfold not in _H1. apply _H1. apply H2.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1.
    unfold not in _H0. apply _H0. apply H0.
  unfold not. intro. inversion_clear H. inversion_clear H0.
    unfold not in _H. apply _H. apply H.
Defined.

Definition bEqual (fs1 fs2 : FragSubst) : bool :=
  if equal fs1 fs2 then true else false.


Lemma Equal_refl : forall fs, Equal fs fs.
Proof.
  intros. destruct fs. constructor. split. apply GRAPH.Equal_refl.
  split. apply GRAPH.Equal_refl. apply LINK.SET.Equal_refl.
Qed.

Lemma Equal_sym : forall fs1 fs2, Equal fs1 fs2 -> Equal fs2 fs1.
Proof.
  intros. destruct fs1 as [p1 r1 bdg1]. destruct fs2 as [p2 r2 bdg2].
  inversion_clear H. inversion_clear H0. inversion_clear H1.
  constructor. apply GRAPH.Equal_sym in H. apply GRAPH.Equal_sym in H0.
  apply LINK.SET.Equal_sym in H2. auto.
Qed.

Lemma Equal_trans : forall fs1 fs2 fs3,
  Equal fs1 fs2 /\ Equal fs2 fs3 -> Equal fs1 fs3.
Proof.
  intros. destruct fs1 as [p1 r1 bdg1]. destruct fs2 as [p2 r2 bdg2].
  destruct fs3 as [p3 r3 bdg3]. constructor. inversion_clear H. inversion_clear H0.
  inversion_clear H1. inversion_clear H. inversion_clear H0. inversion_clear H2.
  inversion_clear H3. split. apply GRAPH.Equal_trans with (g2 := p2). auto.
  split. apply GRAPH.Equal_trans with (g2 := r2). auto.
  apply LINK.SET.Equal_trans with (s2 := bdg2). auto.
Qed.


(* Consistent *)

Inductive Consistent : FragSubst -> Graph -> Prop :=
  | Consistent_ : forall p r bdg gObj gLnk,
                GRAPH.Consistent p (gObj**gLnk) /\ GRAPH.Consistent r (gObj**gLnk)
                /\ LINK.SET.Consistent bdg gLnk -> Consistent (p,.r.,bdg) (gObj**gLnk).

Definition Consistent_dec (fs : FragSubst) (g : Graph) :=
  { Consistent fs g } + { ~Consistent fs g }.

Definition consistent: forall fs g, Consistent_dec fs g.
refine (fix consistent fs g : Consistent_dec fs g :=
  match fs, g with
    | (p,.r.,bdg), (gObj**gLnk) =>
      if GRAPH.consistent p (gObj**gLnk)
      then (if GRAPH.consistent r (gObj**gLnk)
            then (if LINK.SET.consistent bdg gLnk
                  then left _
                  else right _)
            else right _)
      else right _
  end).
Proof.
  constructor. auto.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1. auto.
  unfold not. intro. inversion_clear H. inversion_clear H0. inversion_clear H1. auto.
  unfold not. intro. inversion_clear H. inversion_clear H0. auto.
Defined.

Definition bConsistent (fs : FragSubst) (g : Graph) : bool :=
  if consistent fs g then true else false.


Module SET.


(*  Contains  *)

Inductive Contains : FragSubstSet -> FragSubst -> Prop :=
  | Contains_h : forall fs fs' t, FS.Equal fs fs' -> Contains (fs::t) fs'
  | Contains_t : forall fs h t, Contains t fs -> Contains (h::t) fs.

Definition Contains_dec (fss : FragSubstSet) (fs : FragSubst) := 
  { Contains fss fs } + { ~Contains fss fs }.

Definition contains: forall fss fs, Contains_dec fss fs.
refine (fix contains fss fs: Contains_dec fss fs := 
  match fss with
  | [] => right _
  | h::t => if FS.equal h fs
            then left _
            else if contains t fs
                 then left _
                 else right _
  end).
Proof.
  unfold not. intro. inversion H.
  apply Contains_h. apply _H.
  apply Contains_t. apply _H0.
  unfold not. intro. inversion H. contradiction. contradiction.
Defined.

Definition bContains (fss : FragSubstSet) (fs : FragSubst) : bool :=
  if contains fss fs then true else false.

Lemma Contains_bProp : forall fss fs,
  (bContains fss fs) = true <-> Contains fss fs.
Proof.
  intros. split.
  unfold bContains. destruct (contains fss fs) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bContains. destruct (contains fss fs) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.




(* IsSet *)

Inductive IsSet : FragSubstSet -> Prop :=
  | IsSet_nil  : IsSet []
  | IsSet_cons : forall fss fs, ~Contains fss fs /\ IsSet fss -> IsSet (fs::fss).

Definition IsSet_dec (fss : FragSubstSet) :=
  { IsSet fss } + { ~IsSet fss }.

Definition isSet: forall fss, IsSet_dec fss.
refine (fix isSet fss : IsSet_dec fss :=
  match fss with
  | [] => left _
  | h::t => if contains t h
            then right _
            else if isSet t
                 then left _
                 else right _
  end).
Proof.
  apply IsSet_nil.
  unfold not. intro. inversion H. inversion H1. unfold not in H3. apply H3. apply _H.
  apply IsSet_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H1. unfold not in _H0. apply _H0. apply H4.
Defined.

Definition bIsSet (fss : FragSubstSet) : bool :=
  if isSet fss then true else false.

Lemma IsSet_bProp : forall fss,
  (bIsSet fss) = true <-> IsSet fss.
Proof.
  intros. split.
  unfold bIsSet. destruct (isSet fss) as [T | F].
    intro. apply T.
    intro. inversion H.
  intro. unfold bIsSet. destruct (isSet fss) as [T | F].
    reflexivity.
    exfalso. unfold not in F. apply F. apply H.
Qed.







(* Subset *)

Inductive Subset : FragSubstSet -> FragSubstSet -> Prop :=
  | Subset_nil  : forall fss, Subset [] fss
  | Subset_cons : forall h t fss, Subset t fss /\ Contains fss h -> Subset (h::t) fss.

Definition Subset_dec (fss1 fss2 : FragSubstSet) :=
  { Subset fss1 fss2 } + { ~Subset fss1 fss2 }.

Definition subset: forall fss1 fss2, Subset_dec fss1 fss2.
refine (fix subset fss1 fss2 : Subset_dec fss1 fss2 :=
  match fss1 with
  | [] => left _
  | h::t => if subset t fss2
            then (if contains fss2 h
                  then left _
                  else right _)
            else right _
  end).
Proof.
  apply Subset_nil.
  apply Subset_cons. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H3. unfold not in _H0. apply _H0. apply H5.
  unfold not. intro. inversion H. inversion H3. unfold not in _H. apply _H. apply H4.
Defined.

Definition bSubset (fss1 fss2 : FragSubstSet) : bool :=
  if subset fss1 fss2 then true else false.

Lemma Subset_consR : forall s t h,
  Subset s t -> Subset s (h::t).
Proof.
  intros. induction s as [|h' s'].
    constructor.
    constructor. split. apply IHs'. inversion_clear H. inversion_clear H0. auto.
    inversion_clear H. inversion_clear H0. apply Contains_t. auto.
Qed.

Lemma ContainsEqualFragments : forall fs1 fs2 fss,
  FS.Equal fs1 fs2 /\ Contains fss fs1 -> Contains fss fs2.
Proof.
  intros. induction fss as [|h t].
  inversion_clear H. inversion_clear H1.
  inversion_clear H. inversion_clear H1.
  constructor. apply FS.Equal_trans with (fs2 := fs1). auto.
  apply Contains_t. apply IHt. auto.
Qed.

Lemma Subset_refl : forall fss, Subset fss fss.
Proof.
  intros. induction fss as [|h t].
  constructor.
  constructor. split. apply Subset_consR. auto.
  constructor. apply FS.Equal_refl.
Qed.

Lemma Subset_Contains_trans : forall h fss1 fss2,
  Contains fss1 h /\ Subset fss1 fss2 -> Contains fss2 h.
Proof.
  intros. induction fss1 as [|h1' fss1'].
    inversion_clear H. inversion_clear H0.
    inversion_clear H. inversion_clear H0. inversion_clear H1. inversion_clear H0.
    apply ContainsEqualFragments with (fs1 := h1'). auto.
    apply IHfss1'. inversion_clear H1. inversion_clear H0. auto.
Qed.

Lemma Subset_trans : forall fss1 fss2 fss3,
  Subset fss1 fss2 /\ Subset fss2 fss3 -> Subset fss1 fss3.
Proof.
  intros. induction fss1 as [|h1' fss1'].
  constructor.
  inversion_clear H. inversion_clear H0. inversion_clear H. constructor. split.
    apply IHfss1'. auto.
    apply Subset_Contains_trans with (fss1 := fss2). auto.
Qed.

Lemma SubsetNil : forall fss,
  Subset fss [] -> fss = [].
Proof.
  intros. inversion H. reflexivity. inversion H0. inversion H4.
Qed.







(* Equal *)

Inductive Equal : FragSubstSet -> FragSubstSet -> Prop :=
  | Equal_ : forall fss1 fss2, Subset fss1 fss2 /\ Subset fss2 fss1 -> Equal fss1 fss2.

Definition Equal_dec (fss1 fss2 : FragSubstSet) :=
  { Equal fss1 fss2 } + { ~Equal fss1 fss2 }.

Definition equal: forall fss1 fss2, Equal_dec fss1 fss2.
refine (fix equal fss1 fss2 : Equal_dec fss1 fss2 :=
  if subset fss1 fss2
  then (if subset fss2 fss1
        then left _
        else right _)
  else right _
  ).
Proof.
  apply Equal_. split. apply _H. apply _H0.
  unfold not. intro. inversion H. inversion H0. unfold not in _H0. apply _H0. apply H4.
  unfold not. intro. inversion H. inversion H0. unfold not in _H. apply _H. apply H3.
Defined.

Definition bEqual (fss1 fss2 : FragSubstSet) : bool :=
  if equal fss1 fss2 then true else false.



Lemma Equal_sym : forall fss1 fss2,
  Equal fss1 fss2 -> Equal fss2 fss1.
Proof.
  intros. inversion_clear H. inversion_clear H0. constructor. auto.
Qed.



Lemma Equal_trans : forall fss1 fss2 fss3,
  Equal fss1 fss2 /\ Equal fss2 fss3 -> Equal fss1 fss3.
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. inversion_clear H1.
  inversion_clear H. inversion_clear H0. split. apply Subset_trans with (fss2 := fss2).
  auto. apply Subset_trans with (fss2 := fss2). auto.
Qed.

Lemma EqualNil : forall fss,
  Equal [] fss -> fss = [].
Proof.
  intros. inversion H. inversion H0. inversion H4. reflexivity. inversion H5. inversion H9.
Qed.





(* Consistent *) 

Inductive Consistent : FragSubstSet -> Graph -> Prop :=
  | Consistent_nil  : forall g, Consistent [] g
  | Consistent_cons : forall h t g, FS.Consistent h g /\ Consistent t g
                             -> Consistent (h::t) g.

Definition Consistent_dec (fss : FragSubstSet) (g : Graph) :=
  { Consistent fss g } + { ~Consistent fss g }.

Definition consistent: forall fss g, Consistent_dec fss g.
refine (fix consistent fss g : Consistent_dec fss g :=
  match fss with
  | [] => left _
  | h::t => if FS.consistent h g
            then (if consistent t g
                 then left _
                 else right _)
            else right _
  end).
Proof.
  constructor.
  constructor. auto.
  unfold not. intro. inversion_clear H. inversion_clear H0. auto.
  unfold not. intro. inversion_clear H. inversion_clear H0. auto.
Defined.

Definition bConsistent (fss : FragSubstSet) (g : Graph) : bool :=
  if consistent fss g then true else false.



End SET.

End FS.












Module EXE.


Fixpoint placementObjects (fss : FragSubstSet) : ObjectSet :=
match fss with
  | [] => []
  | (pObj**pLnk,.r.,bdg)::t => OBJECT.SET.union pObj (placementObjects t)
end.

Fixpoint placementLinks (fss : FragSubstSet) : LinkSet :=
match fss with
  | [] => []
  | (pObj**pLnk,.r.,bdg)::t => LINK.SET.union pLnk (placementLinks t)
end.

Fixpoint replacementObjects (fss : FragSubstSet) : ObjectSet :=
match fss with
  | [] => []
  | (p,.rObj**rLnk.,bdg)::t => OBJECT.SET.union rObj (replacementObjects t)
end.

Fixpoint replacementLinks (fss : FragSubstSet) : LinkSet :=
match fss with
  | [] => []
  | (p,.rObj**rLnk.,bdg)::t => LINK.SET.union rLnk (replacementLinks t)
end.

Fixpoint bindingLinks (fss : FragSubstSet) : LinkSet :=
match fss with
  | [] => []
  | (p,.r.,bdg)::t => LINK.SET.union bdg (bindingLinks t)
end.

Fixpoint allObjects (fss : FragSubstSet) : ObjectSet :=
match fss with
  | [] => []
  | (pObj**pLnk,.rObj**rLnk.,bdg)::t =>
            OBJECT.SET.union pObj (OBJECT.SET.union rObj (allObjects t))
end.

Fixpoint allLinks (fss : FragSubstSet) : LinkSet :=
match fss with
  | [] => []
  | (pObj**pLnk,.rObj**rLnk.,bdg)::t =>
        LINK.SET.union pLnk (LINK.SET.union rLnk
          (LINK.SET.union bdg (allLinks t)))
end.



(* placement lemmas *)

Theorem PlacementObjectsExecutes : forall fss pObj pLnk r b,
  FS.SET.Contains fss (pObj**pLnk,.r.,b)
  -> OBJECT.SET.Subset pObj (placementObjects fss).
Proof.
  intros. induction fss as [|fs t].
  - inversion H.
  - inversion_clear H.
    + unfold placementObjects. fold placementObjects.
      destruct fs as [[p1Obj p1Lnk] r1 bdg1]. inversion_clear H0.
      inversion_clear H. inversion_clear H0. inversion_clear H.
      inversion_clear H0. inversion_clear H.
      apply OBJECT.SET.SubsetsUnionLeft. auto.
    + apply IHt in H0. unfold placementObjects. fold EXE.placementObjects.
      destruct fs as [[p1Obj p1Lnk] r1 bdg1].
      apply OBJECT.SET.SubsetsUnionRight. auto.
Qed.


Theorem PlacementLinksExecutes : forall fss pObj pLnk r b,
  FS.SET.Contains fss (pObj**pLnk,.r.,b)
  -> LINK.SET.Subset pLnk (placementLinks fss).
Proof.
  intros. induction fss as [|fs t].
  - inversion H.
  - inversion_clear H.
    + simpl. destruct fs as [[p1Obj p1Lnk] r1 bdg1]. inversion_clear H0.
      inversion_clear H. inversion_clear H0. inversion_clear H.
      inversion_clear H2. inversion_clear H.
      apply LINK.SET.SubsetsUnionLeft. auto.
    + apply IHt in H0. simpl. destruct fs as [[p1Obj p1Lnk] r1 bdg1].
    apply LINK.SET.SubsetsUnionRight. auto.
Qed.

Theorem PlacementObjectsOfSubsetFss : forall fss1 fss2,
  FS.SET.Subset fss1 fss2
  -> OBJECT.SET.Subset (placementObjects fss1) (placementObjects fss2).
Proof.
  intros. induction fss1 as [|fs t].
  - simpl. constructor.
  - inversion_clear H. inversion_clear H0. apply IHt in H.
    destruct fs as [[pObj pLnk] r b]. simpl.
    apply PlacementObjectsExecutes in H1. apply OBJECT.SET.UnionSubset.
    split. auto. auto.
Qed.

Theorem PlacementLinksOfSubsetFss : forall fss1 fss2,
  FS.SET.Subset fss1 fss2
  -> LINK.SET.Subset (placementLinks fss1) (placementLinks fss2).
Proof.
  intros. induction fss1 as [|fs t].
  - simpl. constructor.
  - inversion_clear H. inversion_clear H0. apply IHt in H.
    destruct fs as [[pObj pLnk] r bdg]. simpl.
    apply PlacementLinksExecutes in H1. apply LINK.SET.UnionSubset.
    split. auto. auto.
Qed.

Theorem PlacementObjectsOfEqualFss : forall fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> OBJECT.SET.Equal (placementObjects fss1) (placementObjects fss2).
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. split.
  - apply PlacementObjectsOfSubsetFss. auto.
  - apply PlacementObjectsOfSubsetFss. auto.
Qed.

Theorem PlacementLinksOfEqualFss : forall fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> LINK.SET.Equal (placementLinks fss1) (placementLinks fss2).
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. split.
  - apply PlacementLinksOfSubsetFss. auto.
  - apply PlacementLinksOfSubsetFss. auto.
Qed.


(* replacement lemmas *)

Theorem ReplacementObjectsExecutes : forall fss p rObj rLnk b,
  FS.SET.Contains fss (p,.rObj**rLnk.,b)
  -> OBJECT.SET.Subset rObj (replacementObjects fss).
Proof.
  intros. induction fss as [|fs t].
  - inversion H.
  - inversion_clear H.
    + simpl. destruct fs as [p1 [r1Obj r1Lnk] bdg1]. inversion_clear H0.
      inversion_clear H. inversion_clear H1. inversion_clear H.
      inversion_clear H1. inversion_clear H. inversion_clear H1.
      apply OBJECT.SET.SubsetsUnionLeft. auto.
    + apply IHt in H0. simpl. destruct fs as [p1 [r1Obj r1Lnk] bdg1].
      apply OBJECT.SET.SubsetsUnionRight. auto.
Qed.


Theorem ReplacementLinksExecutes : forall fss p rObj rLnk b,
  FS.SET.Contains fss (p,.rObj**rLnk.,b)
  -> LINK.SET.Subset rLnk (replacementLinks fss).
Proof.
  intros. induction fss as [|fs t].
  - inversion H.
  - inversion_clear H.
    + simpl. destruct fs as [p1 [r1Obj r1Lnk] bdg1]. inversion_clear H0.
      inversion_clear H. inversion_clear H1. inversion_clear H.
      inversion_clear H1. inversion_clear H3. inversion_clear H1.
      apply LINK.SET.SubsetsUnionLeft. auto.
    + apply IHt in H0. simpl. destruct fs as [p1 [r1Obj r1Lnk] bdg1].
    apply LINK.SET.SubsetsUnionRight. auto.
Qed.

Theorem ReplacementObjectsOfSubsetFss : forall fss1 fss2,
  FS.SET.Subset fss1 fss2
  -> OBJECT.SET.Subset (replacementObjects fss1) (replacementObjects fss2).
Proof.
  intros. induction fss1 as [|fs t].
  - simpl. constructor.
  - inversion_clear H. inversion_clear H0. apply IHt in H.
    destruct fs as [p [rObj rLnk] b]. simpl.
    apply ReplacementObjectsExecutes in H1. apply OBJECT.SET.UnionSubset.
    split. auto. auto.
Qed.

Theorem ReplacementLinksOfSubsetFss : forall fss1 fss2,
  FS.SET.Subset fss1 fss2
  -> LINK.SET.Subset (replacementLinks fss1) (replacementLinks fss2).
Proof.
  intros. induction fss1 as [|fs t].
  - simpl. constructor.
  - inversion_clear H. inversion_clear H0. apply IHt in H.
    destruct fs as [p [rObj rLnk] bdg]. simpl.
    apply ReplacementLinksExecutes in H1. apply LINK.SET.UnionSubset.
    split. auto. auto.
Qed.

Theorem ReplacementObjectsOfEqualFss : forall fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> OBJECT.SET.Equal (replacementObjects fss1) (replacementObjects fss2).
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. split.
  - apply ReplacementObjectsOfSubsetFss. auto.
  - apply ReplacementObjectsOfSubsetFss. auto.
Qed.

Theorem ReplacementLinksOfEqualFss : forall fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> LINK.SET.Equal (replacementLinks fss1) (replacementLinks fss2).
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. split.
  - apply ReplacementLinksOfSubsetFss. auto.
  - apply ReplacementLinksOfSubsetFss. auto.
Qed.



(* binding lemmas *)

Theorem BindingLinksExecutes : forall fss p r b,
  FS.SET.Contains fss (p,.r.,b)
  -> LINK.SET.Subset b (bindingLinks fss).
Proof.
  intros. induction fss as [|fs t].
  - inversion H.
  - inversion_clear H.
    + simpl. destruct fs as [p1 r1 bdg1]. inversion_clear H0.
      inversion_clear H. inversion_clear H1. inversion_clear H2.
      inversion_clear H1.
      apply LINK.SET.SubsetsUnionLeft. auto.
    + apply IHt in H0. simpl. destruct fs as [p1 r1 bdg1].
    apply LINK.SET.SubsetsUnionRight. auto.
Qed.

Theorem BindingLinksOfSubsetFss : forall fss1 fss2,
  FS.SET.Subset fss1 fss2
  -> LINK.SET.Subset (bindingLinks fss1) (bindingLinks fss2).
Proof.
  intros. induction fss1 as [|fs t].
  - simpl. constructor.
  - inversion_clear H. inversion_clear H0. apply IHt in H.
    destruct fs as [p r bdg]. simpl.
    apply BindingLinksExecutes in H1. apply LINK.SET.UnionSubset.
    split. auto. auto.
Qed.

Theorem BindingLinksOfEqualFss : forall fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> LINK.SET.Equal (bindingLinks fss1) (bindingLinks fss2).
Proof.
  intros. constructor. inversion_clear H. inversion_clear H0. split.
  - apply BindingLinksOfSubsetFss. auto.
  - apply BindingLinksOfSubsetFss. auto.
Qed.




(* copy functions *)


Fixpoint objCopy (fObj : ObjectSet) (fss : FragSubstSet) : ObjectSet :=
match fObj with
  | [] => []
  | h::t => if OBJECT.SET.bContains (replacementObjects fss) h
            && !(OBJECT.SET.bContains (placementObjects fss) h)
            then h::(objCopy t fss)
            else (objCopy t fss)
end.

Fixpoint lnkCopy (fLnk : LinkSet) (fss : FragSubstSet) : LinkSet :=
match fLnk with
  | [] => []
  | (id¤src-->tgt)::t =>
         if (LINK.SET.bContainsId (replacementLinks fss) (id¤src-->tgt)
         || LINK.SET.bContainsId (bindingLinks fss) (id¤src-->tgt))
         && !(LINK.SET.bContainsId (placementLinks fss) (id¤src-->tgt))
         && !(OBJECT.SET.bContains (placementObjects fss) src)
         && !(OBJECT.SET.bContains (placementObjects fss) tgt)
         then (id¤src-->tgt)::(lnkCopy t fss)
         else (lnkCopy t fss)
end.

Function executeFss (fss : FragSubstSet) : Model :=
  (objCopy (allObjects fss) fss)**(lnkCopy (allLinks fss) fss).







Theorem objCopyExecutes : forall o fObj fss,
  OBJECT.SET.Contains fObj o
  /\ OBJECT.SET.Contains (replacementObjects fss) o
  /\ ~OBJECT.SET.Contains (placementObjects fss) o
  <-> OBJECT.SET.Contains (objCopy fObj fss) o.
Proof.
  intros. split.
  { intros. inversion_clear H. inversion_clear H1. induction fObj as [|h t].
    - inversion_clear H0.
    - simpl. inversion H0.
      * apply OBJECT.SET.Contains_bProp in H. rewrite H.
        apply OBJECT.SET.NotContains_bProp in H2. rewrite H2. simpl.
        constructor.
      * { destruct (OBJECT.SET.bContains (replacementObjects fss) h &&
        !(OBJECT.SET.bContains (placementObjects fss) h)).
        - constructor. apply IHt. auto.
        - apply IHt. auto. } }
  { intros. split.
    - induction fObj as [|h t].
      + inversion H.
      + simpl in H.
        destruct (OBJECT.SET.bContains (replacementObjects fss) h &&
        !(OBJECT.SET.bContains (placementObjects fss) h)) eqn: cond.
        * inversion H. constructor. constructor. auto.
        * constructor. auto.
    - induction fObj as [|h t].
      + inversion H.
      + simpl in H. 
        destruct (OBJECT.SET.bContains (replacementObjects fss) h &&
        !(OBJECT.SET.bContains (placementObjects fss) h)) eqn: cond.
        * { apply Bool.andb_true_iff in cond. inversion_clear cond.
          apply OBJECT.SET.Contains_bProp in H0.
          apply Bool.negb_true_iff in H1.
          apply OBJECT.SET.NotContains_bProp in H1. inversion H.
          - subst o. auto.
          - auto. }
        * auto. }
Qed.



Theorem lnkCopyExecutes : forall id src tgt fLnk fss,
  LINK.SET.Contains fLnk (id ¤ src --> tgt)
  /\ (LINK.SET.ContainsId (replacementLinks fss) (id ¤ src --> tgt)
    \/ LINK.SET.ContainsId (bindingLinks fss) (id ¤ src --> tgt))
  /\ ~LINK.SET.ContainsId (placementLinks fss) (id ¤ src --> tgt)
  /\ ~OBJECT.SET.Contains (placementObjects fss) src
  /\ ~OBJECT.SET.Contains (placementObjects fss) tgt
  <-> LINK.SET.Contains (lnkCopy fLnk fss) (id ¤ src --> tgt).
Proof.
  intros. split.
  { intros. inversion_clear H. inversion_clear H1. inversion_clear H2.
    inversion_clear H3. induction fLnk as [|h t].
    - inversion_clear H0.
    - destruct h as [idh srch tgth]. simpl. inversion_clear H0.
      + inversion_clear H3. inversion_clear H0. inversion_clear H5.
        subst idh. subst srch. subst tgth.
        apply LINK.SET.NotContainsId_bProp in H1. rewrite H1.
        apply OBJECT.SET.NotContains_bProp in H2. rewrite H2.
        apply OBJECT.SET.NotContains_bProp in H4. rewrite H4.
        inversion_clear H.
        * apply LINK.SET.ContainsId_bProp in H0. rewrite H0. simpl. constructor.
          apply LINK.Equal_refl.
        * apply LINK.SET.ContainsId_bProp in H0. rewrite H0.
          assert (H : (LINK.SET.bContainsId (replacementLinks fss) (id ¤ src --> tgt)
            || true) && !false && !false && !false = true).
          { simpl. apply Bool.andb_true_iff. split. apply Bool.andb_true_iff. split.
            apply Bool.andb_true_iff. split. apply Bool.orb_true_iff. right. reflexivity.
            reflexivity. reflexivity. reflexivity. } rewrite H. constructor.
          apply LINK.Equal_refl.
      + destruct (
          (LINK.SET.bContainsId (replacementLinks fss) (idh ¤ srch --> tgth)
            || LINK.SET.bContainsId (bindingLinks fss) (idh ¤ srch --> tgth)) &&
          !(LINK.SET.bContainsId (placementLinks fss) (idh ¤ srch --> tgth)) &&
          !(OBJECT.SET.bContains (placementObjects fss) srch) &&
          !(OBJECT.SET.bContains (placementObjects fss) tgth)).
        * constructor 2. apply IHt. auto.
        * apply IHt. auto. }
  { intros. split.
    - induction fLnk as [|h t].
      + inversion H.
      + destruct h as [idh srch tgth]. simpl in H.
        destruct (
          (LINK.SET.bContainsId (replacementLinks fss) (idh ¤ srch --> tgth)
           || LINK.SET.bContainsId (bindingLinks fss) (idh ¤ srch --> tgth)) &&
          !(LINK.SET.bContainsId (placementLinks fss) (idh ¤ srch --> tgth)) &&
          !(OBJECT.SET.bContains (placementObjects fss) srch) &&
          !(OBJECT.SET.bContains (placementObjects fss) tgth)) eqn: cond.
        * { inversion_clear H.
          - apply LINK.Equal_eq in H0. rewrite H0. constructor.
            apply LINK.Equal_refl.
          - constructor 2. auto. }
        * constructor 2. auto.
    - induction fLnk as [|h t].
      + inversion H.
      + destruct h as [idh srch tgth]. simpl in H.
        destruct (
          (LINK.SET.bContainsId (replacementLinks fss) (idh ¤ srch --> tgth)
           || LINK.SET.bContainsId (bindingLinks fss) (idh ¤ srch --> tgth)) &&
          !(LINK.SET.bContainsId (placementLinks fss) (idh ¤ srch --> tgth)) &&
          !(OBJECT.SET.bContains (placementObjects fss) srch) &&
          !(OBJECT.SET.bContains (placementObjects fss) tgth)) eqn: cond.
        * { apply Bool.andb_true_iff in cond. inversion_clear cond.
          apply Bool.andb_true_iff in H0. inversion_clear H0.
          apply Bool.andb_true_iff in H2. inversion_clear H2.
          apply Bool.negb_true_iff in H4.
          apply LINK.SET.NotContainsId_bProp in H4.
          apply Bool.negb_true_iff in H1.
          apply OBJECT.SET.NotContains_bProp in H1.
          apply Bool.negb_true_iff in H3.
          apply OBJECT.SET.NotContains_bProp in H3.
          apply Bool.orb_true_iff in H0. inversion_clear H0.
          - apply LINK.SET.ContainsId_bProp in H2. inversion_clear H.
            + inversion_clear H0. inversion_clear H. inversion_clear H5. subst idh.
              subst srch. subst tgth. split. left. auto. auto.
            + apply IHt. auto.
          - apply LINK.SET.ContainsId_bProp in H2. inversion_clear H.
            + inversion_clear H0. inversion_clear H. inversion_clear H5. subst idh.
              subst srch. subst tgth. split. right. auto. auto.
            + auto. }
        * auto. }
Qed.




(* confluence *)

Theorem objCopyOnEqualFss : forall obj fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> OBJECT.SET.Equal (objCopy obj fss1) (objCopy obj fss2).
Proof.
  intros. induction obj as [|h t].
  - simpl. apply OBJECT.SET.Equal_refl.
  - simpl.
    destruct (OBJECT.SET.bContains (replacementObjects fss1) h) eqn:fss1rep.
    + assert (fss2rep :
      OBJECT.SET.bContains (replacementObjects fss2) h = true).
      { apply OBJECT.SET.Contains_bProp.
        apply OBJECT.SET.Contains_bProp in fss1rep.
        apply OBJECT.SET.EqualSetsContainSameObjects
          with (s1 := replacementObjects fss1).
        split. apply ReplacementObjectsOfEqualFss. auto. auto. }
      rewrite fss2rep. simpl.
      destruct (OBJECT.SET.bContains (placementObjects fss1) h) eqn:fss1pl.
      * assert (fss2pl :
        OBJECT.SET.bContains (placementObjects fss2) h = true).
        { apply OBJECT.SET.Contains_bProp.
          apply OBJECT.SET.Contains_bProp in fss1pl.
          apply OBJECT.SET.EqualSetsContainSameObjects
            with (s1 := placementObjects fss1).
          split. apply PlacementObjectsOfEqualFss. auto. auto. }
        rewrite fss2pl. simpl. auto.
      * { destruct (OBJECT.SET.bContains (placementObjects fss2) h)
          eqn:fss2pl.
        - assert (fss1pl' :
            OBJECT.SET.bContains (placementObjects fss1) h = true).
          { apply OBJECT.SET.Contains_bProp.
            apply OBJECT.SET.Contains_bProp in fss2pl.
            apply OBJECT.SET.EqualSetsContainSameObjects
              with (s1 := placementObjects fss2). split.
            - apply OBJECT.SET.Equal_sym. assert (H1 := H).
              apply PlacementObjectsOfEqualFss in H1. auto.
            - auto. }
          rewrite fss1pl' in fss1pl. inversion fss1pl.
        - simpl. inversion_clear IHt. inversion_clear H0. constructor. split.
           + constructor. split.
             * apply OBJECT.SET.SubsetRight. auto.
             * constructor.
           + apply OBJECT.SET.SubsetH. auto. }
    + simpl. destruct (
      OBJECT.SET.bContains (replacementObjects fss2) h) eqn:fss2rep.
      * assert (fss1rep' :
        OBJECT.SET.bContains (replacementObjects fss1) h = true).
        { apply OBJECT.SET.Contains_bProp.
          apply OBJECT.SET.Contains_bProp in fss2rep.
          apply OBJECT.SET.EqualSetsContainSameObjects
            with (s1 := replacementObjects fss2). split.
          - apply ReplacementObjectsOfEqualFss. apply FS.SET.Equal_sym. auto.
          - auto. }
        rewrite fss1rep in fss1rep'. inversion fss1rep'.
      * simpl. auto.
Qed.

Theorem lnkCopyOnEqualFss : forall lnk fss1 fss2,
  FS.SET.Equal fss1 fss2
  -> LINK.SET.Equal (lnkCopy lnk fss1) (lnkCopy lnk fss2).
Proof.
  intros. induction lnk as [|h t].
  - simpl. apply LINK.SET.Equal_refl.
  - simpl. destruct h as [idh srch tgth]. destruct (
      !(LINK.SET.bContainsId (placementLinks fss1) (idh ¤ srch --> tgth))) eqn:fss1pl.
    + assert (fss2pl :
      !(LINK.SET.bContainsId (placementLinks fss2) (idh ¤ srch --> tgth)) = true).
      { apply Bool.negb_true_iff. apply LINK.SET.NotContainsId_bProp.
        apply Bool.negb_true_iff in fss1pl.
        apply LINK.SET.NotContainsId_bProp in fss1pl. assert (H1 := H).
        apply PlacementLinksOfEqualFss in H1. intro. apply fss1pl.
        apply LINK.SET.EqualSetsContainSameLinks with (s1 := EXE.placementLinks fss2).
        split. apply LINK.SET.Equal_sym. auto. auto. }
      rewrite fss2pl.
      destruct (!(OBJECT.SET.bContains (placementObjects fss1) srch)) eqn:fss1src.
      * assert (fss2src : !(OBJECT.SET.bContains (placementObjects fss2) srch) = true).
        { apply Bool.negb_true_iff. apply OBJECT.SET.NotContains_bProp.
          apply Bool.negb_true_iff in fss1src.
          apply OBJECT.SET.NotContains_bProp in fss1src.
          assert (H1 := H). apply PlacementObjectsOfEqualFss in H1.
          intro. apply fss1src.
          apply OBJECT.SET.EqualSetsContainSameObjects
            with (s1 := EXE.placementObjects fss2).
          split. apply OBJECT.SET.Equal_sym. auto. auto. }
        rewrite fss2src.
        { destruct (!(OBJECT.SET.bContains (placementObjects fss1) tgth)) eqn:fss1tgt.
        - assert (fss2tgt : !(OBJECT.SET.bContains (placementObjects fss2) tgth) = true).
          { apply Bool.negb_true_iff.
            apply OBJECT.SET.NotContains_bProp.
            apply Bool.negb_true_iff in fss1tgt.
            apply OBJECT.SET.NotContains_bProp in fss1tgt.
            assert (H1 := H). apply PlacementObjectsOfEqualFss in H1.
            intro. apply fss1tgt.
            apply OBJECT.SET.EqualSetsContainSameObjects
              with (s1 := EXE.placementObjects fss2).
            split. apply OBJECT.SET.Equal_sym. auto. auto. }
          rewrite fss2tgt. destruct (
            LINK.SET.bContainsId (replacementLinks fss1) (idh ¤ srch --> tgth)) eqn:fss1rep.
          + assert (fss2rep :
              LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth) = true).
            { apply LINK.SET.ContainsId_bProp in fss1rep.
              apply LINK.SET.ContainsId_bProp. assert (H1 := H).
              apply ReplacementLinksOfEqualFss in H1.
              apply LINK.SET.EqualSetsContainSameLinks
                with (s1 := replacementLinks fss1). split. auto. auto. }
              rewrite fss2rep. simpl. constructor. split.
              * constructor. { split.
                - apply LINK.SET.SubsetRight. inversion_clear IHt. inversion_clear H0. auto.
                - constructor. apply LINK.EqualId_refl. }
              * constructor. { split.
                - apply LINK.SET.SubsetRight. inversion_clear IHt. inversion_clear H0. auto.
                - constructor. apply LINK.EqualId_refl. }
          + destruct (
              LINK.SET.bContainsId (bindingLinks fss1) (idh ¤ srch --> tgth)) eqn:fss1bdg.
            * assert (fss2bdg :
                LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth) = true).
              { apply LINK.SET.ContainsId_bProp in fss1bdg.
                apply LINK.SET.ContainsId_bProp. assert (H1 := H).
                apply BindingLinksOfEqualFss in H1.
                apply LINK.SET.EqualSetsContainSameLinks
                  with (s1 := bindingLinks fss1). split. auto. auto. }
              assert (H1 :
                (LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth)
                || LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth)) &&
                true && true && true = true).
              { apply Bool.andb_true_iff. split. apply Bool.andb_true_iff. split.
                apply Bool.andb_true_iff. split. apply Bool.orb_true_iff. right.
                rewrite fss2bdg. reflexivity. reflexivity. reflexivity. reflexivity.
              } rewrite H1. simpl. constructor. { split.
              - constructor. split.
                + apply LINK.SET.SubsetRight. inversion_clear IHt. inversion_clear H0. auto.
                + constructor. apply LINK.EqualId_refl.
              - constructor. split.
                + apply LINK.SET.SubsetRight. inversion_clear IHt. inversion_clear H0. auto.
                + constructor. apply LINK.EqualId_refl. }
            * { destruct (
                LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth)) eqn:fss2bdg.
              - assert (fss1bdg' :
                  LINK.SET.bContainsId (bindingLinks fss1) (idh ¤ srch --> tgth) = true).
                { apply LINK.SET.ContainsId_bProp in fss2bdg.
                  apply LINK.SET.ContainsId_bProp. assert (H1 := H).
                  apply BindingLinksOfEqualFss in H1.
                  apply LINK.SET.EqualSetsContainSameLinks
                    with (s1 := bindingLinks fss2). split. apply LINK.SET.Equal_sym.
                  auto. auto. }
                rewrite fss1bdg' in fss1bdg. inversion fss1bdg.
              - destruct (
                  LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth))
                  eqn:fss2rep.
                + assert (fss1rep' :
                    LINK.SET.bContainsId (replacementLinks fss1) (idh ¤ srch --> tgth)
                    = true).
                  { apply LINK.SET.ContainsId_bProp in fss2rep.
                    apply LINK.SET.ContainsId_bProp. assert (H1 := H).
                    apply ReplacementLinksOfEqualFss in H1.
                    apply LINK.SET.EqualSetsContainSameLinks
                      with (s1 := replacementLinks fss2). split. apply LINK.SET.Equal_sym.
                    auto. auto. }
                  rewrite fss1rep' in fss1rep. inversion fss1rep.
                + simpl. auto. }
        - destruct (!(OBJECT.SET.bContains (placementObjects fss2) tgth)) eqn:fss2tgt.
          + assert (fss1tgt' : !(OBJECT.SET.bContains (placementObjects fss1) tgth) = true).
            { apply Bool.negb_true_iff. apply OBJECT.SET.NotContains_bProp.
              apply Bool.negb_true_iff in fss2tgt.
              apply OBJECT.SET.NotContains_bProp in fss2tgt. assert (H1 := H).
              apply PlacementObjectsOfEqualFss in H1. intro. apply fss2tgt.
              apply OBJECT.SET.EqualSetsContainSameObjects
                with (s1 := EXE.placementObjects fss1).
              split. auto. auto. }
            rewrite fss1tgt' in fss1tgt. inversion fss1tgt.
          + assert (H1 :
              (LINK.SET.bContainsId (replacementLinks fss1) (idh ¤ srch --> tgth)
              || LINK.SET.bContainsId (bindingLinks fss1) (idh ¤ srch --> tgth)) &&
              true && true && false = false). apply Bool.andb_false_r.
            assert (H2 :
              (LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth)
              || LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth)) &&
              true && true && false = false). apply Bool.andb_false_r.
            rewrite H1. rewrite H2. apply IHt. }
      * { destruct (!(OBJECT.SET.bContains (placementObjects fss2) srch)) eqn:fss2src.
        - assert (fss1src' : !(OBJECT.SET.bContains (placementObjects fss1) srch) = true).
          { apply Bool.negb_true_iff. apply OBJECT.SET.NotContains_bProp.
            apply Bool.negb_true_iff in fss2src.
            apply OBJECT.SET.NotContains_bProp in fss2src. assert (H1 := H).
            apply PlacementObjectsOfEqualFss in H1. intro. apply fss2src.
            apply OBJECT.SET.EqualSetsContainSameObjects
              with (s1 := EXE.placementObjects fss1).
            split. auto. auto. }
          rewrite fss1src' in fss1src. inversion fss1src.
        - assert (H1 : (LINK.SET.bContainsId (replacementLinks fss1) (idh ¤ srch --> tgth)
            || LINK.SET.bContainsId (bindingLinks fss1) (idh ¤ srch --> tgth)) &&
            true && false && !(OBJECT.SET.bContains (placementObjects fss1) tgth) = false).
          { apply Bool.andb_false_iff. left. apply Bool.andb_false_r. }
          assert (H2 : (LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth)
            || LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth)) &&
            true && false && !(OBJECT.SET.bContains (placementObjects fss2) tgth) = false).
          { apply Bool.andb_false_iff. left. apply Bool.andb_false_r. }
          rewrite H1. rewrite H2. apply IHt. }
    + destruct (
      !(LINK.SET.bContainsId (placementLinks fss2) (idh ¤ srch --> tgth))) eqn:fss2pl.
      * assert (fss1pl' :
          !(LINK.SET.bContainsId (placementLinks fss1) (idh ¤ srch --> tgth)) = true).
        { apply Bool.negb_true_iff. apply LINK.SET.NotContainsId_bProp.
          apply Bool.negb_true_iff in fss2pl.
          apply LINK.SET.NotContainsId_bProp in fss2pl. assert (H1 := H).
          apply PlacementLinksOfEqualFss in H1. intro. apply fss2pl.
          apply LINK.SET.EqualSetsContainSameLinks with (s1 := EXE.placementLinks fss1).
          split. auto. auto. }
        rewrite fss1pl' in fss1pl. inversion fss1pl.
      * assert (H1 : (LINK.SET.bContainsId (replacementLinks fss1) (idh ¤ srch --> tgth)
          || LINK.SET.bContainsId (bindingLinks fss1) (idh ¤ srch --> tgth)) &&
          false && !(OBJECT.SET.bContains (placementObjects fss1) srch) &&
          !(OBJECT.SET.bContains (placementObjects fss1) tgth) = false).
        { apply Bool.andb_false_iff. left. apply Bool.andb_false_iff. left.
          apply Bool.andb_false_r. }
        assert (H2 : (LINK.SET.bContainsId (replacementLinks fss2) (idh ¤ srch --> tgth)
          || LINK.SET.bContainsId (bindingLinks fss2) (idh ¤ srch --> tgth)) &&
          false && !(OBJECT.SET.bContains (placementObjects fss2) srch) &&
          !(OBJECT.SET.bContains (placementObjects fss2) tgth) = false).
        { apply Bool.andb_false_iff. left. apply Bool.andb_false_iff. left.
          apply Bool.andb_false_r. }
        rewrite H1. rewrite H2. apply IHt.
Qed.


Theorem objCopyOfSubset : forall obj1 obj2 fss,
  OBJECT.SET.Subset obj1 obj2
  -> OBJECT.SET.Subset (objCopy obj1 fss) (objCopy obj2 fss).
Proof.
  intros. induction obj1 as [|h t].
  - simpl. constructor.
  - simpl. destruct (OBJECT.SET.bContains (replacementObjects fss) h &&
      !(OBJECT.SET.bContains (placementObjects fss) h)) eqn:test.
    + constructor. split.
      * apply IHt. inversion_clear H. inversion_clear H0. auto.
      * inversion_clear H. inversion_clear H0. apply objCopyExecutes.
        split. auto. apply Bool.andb_true_iff in test. inversion_clear test.
        apply OBJECT.SET.Contains_bProp in H0.
        apply Bool.negb_true_iff in H2.
        apply OBJECT.SET.NotContains_bProp in H2. auto.
    + inversion_clear H. inversion_clear H0. apply IHt. auto.
Qed.

Theorem objCopyOfEqualSets : forall obj1 obj2 fss,
  OBJECT.SET.Equal obj1 obj2
  -> OBJECT.SET.Equal (objCopy obj1 fss) (objCopy obj2 fss).
Proof.
  intros. inversion_clear H. inversion_clear H0. constructor. split.
  - apply objCopyOfSubset. auto.
  - apply objCopyOfSubset. auto.
Qed.



Theorem lnkCopyOfSubset : forall lnk1 lnk2 lnkbase fss,
  LINK.SET.Subset lnk1 lnk2
  /\ LINK.SET.Consistent lnk1 lnkbase /\ LINK.SET.Consistent lnk2 lnkbase
  -> LINK.SET.Subset (lnkCopy lnk1 fss) (lnkCopy lnk2 fss).
Proof.
  intros. induction lnk1 as [|h t].
  - simpl. inversion_clear H. constructor.
  - simpl. destruct h as [idh srch tgth].
    destruct (
      (LINK.SET.bContainsId (replacementLinks fss) (idh ¤ srch --> tgth)
       || LINK.SET.bContainsId (bindingLinks fss) (idh ¤ srch --> tgth)) &&
      !(LINK.SET.bContainsId (placementLinks fss) (idh ¤ srch --> tgth)) &&
      !(OBJECT.SET.bContains (placementObjects fss) srch) &&
      !(OBJECT.SET.bContains (placementObjects fss) tgth)) eqn:test.
    + constructor. split.
      * apply IHt. { split.
        - inversion_clear H. inversion_clear H0. inversion_clear H. auto.
        - split.
          + inversion_clear H. inversion_clear H1. inversion_clear H.
            inversion_clear H1. inversion_clear H3. inversion_clear H4.
            auto.
          + inversion_clear H. inversion_clear H1. auto. }
      * assert (H3 :
          LINK.SET.Contains (lnkCopy lnk2 fss) (idh ¤ srch --> tgth)).
        { apply lnkCopyExecutes. split.
          { apply LINK.SET.ExtractConsistentLink with (mLnk:=lnkbase). split.
            - inversion_clear H. inversion_clear H0. inversion_clear H. auto.
            - split.
              + inversion_clear H. inversion_clear H1. inversion_clear H.
                inversion_clear H1. inversion_clear H3. inversion_clear H4.
                auto.
              + inversion_clear H. inversion_clear H1. auto.
          } apply Bool.andb_true_iff in test. inversion_clear test.
          apply Bool.andb_true_iff in H0. inversion_clear H0.
          apply Bool.andb_true_iff in H2. inversion_clear H2.
          apply Bool.orb_true_iff in H0. inversion_clear H0.
          - apply LINK.SET.ContainsId_bProp in H2.
            apply Bool.negb_true_iff in H4.
            apply LINK.SET.NotContainsId_bProp in H4.
            apply Bool.negb_true_iff in H1.
            apply OBJECT.SET.NotContains_bProp in H1.
            apply Bool.negb_true_iff in H3.
            apply OBJECT.SET.NotContains_bProp in H3. auto.
          - apply LINK.SET.ContainsId_bProp in H2.
            apply Bool.negb_true_iff in H4.
            apply LINK.SET.NotContainsId_bProp in H4.
            apply Bool.negb_true_iff in H1.
            apply OBJECT.SET.NotContains_bProp in H1.
            apply Bool.negb_true_iff in H3.
            apply OBJECT.SET.NotContains_bProp in H3. auto.
        } apply LINK.SET.ContainsImpliesContainsId in H3. auto.
    + apply IHt. split.
      * inversion_clear H. inversion_clear H0. inversion_clear H. auto.
      * { split.
        - inversion_clear H. inversion_clear H1. inversion_clear H.
          inversion_clear H1. inversion_clear H3. inversion_clear H4. auto.
        - inversion_clear H. inversion_clear H1. auto. }
Qed.


Theorem lnkCopyOfEqualSets : forall lnk1 lnk2 lnkbase fss,
  LINK.SET.Equal lnk1 lnk2
  /\ LINK.SET.Consistent lnk1 lnkbase /\ LINK.SET.Consistent lnk2 lnkbase
  -> LINK.SET.Equal (lnkCopy lnk1 fss) (lnkCopy lnk2 fss).
Proof.
  intros. inversion_clear H. inversion_clear H1. inversion_clear H0.
  inversion_clear H1. constructor. split.
  - apply lnkCopyOfSubset with (lnkbase:=lnkbase). auto.
  - apply lnkCopyOfSubset with (lnkbase:=lnkbase). auto.
Qed.

End EXE.


Definition model : Model :=
  [1; 2; 3; 4; 5; 6; 7]**
  [1¤3-->1; 2¤1-->2; 3¤3-->2; 4¤1-->4; 5¤6-->5; 6¤3-->5; 7¤7-->5; 8¤6-->7].

Definition fss : FragSubstSet :=
[ ([  ]**[  ],.[ 1; 2; 3; 4; 5; 6; 7; 8; 9; 10 ]**[ 1¤1-->2; 2¤2-->3; 3¤3-->4; 4¤3-->5; 5¤5-->6; 6¤6-->2; 7¤6-->5; 8¤6-->7; 9¤6-->8; 10¤5-->6; 11¤5-->3; 12¤3-->9; 13¤3-->10; 14¤1-->4; 15¤1-->5 ].,[  ]);
 ([ 90; 91; 92; 93; 94; 95; 96; 97 ]**[ 160¤90-->91; 161¤91-->90; 162¤91-->92; 163¤91-->93; 164¤90-->91; 165¤90-->94; 166¤94-->95; 167¤94-->90; 168¤94-->96; 169¤94-->97 ],.[ 98; 99; 100; 101; 102; 103; 104; 105 ]**[ 170¤98-->99; 171¤99-->98; 172¤99-->100; 173¤99-->101; 174¤98-->99; 175¤98-->102; 176¤102-->103; 177¤102-->98; 178¤102-->104; 179¤102-->105 ].,[ 180¤170-->98; 181¤170-->103; 182¤122-->102; 183¤99-->122 ]);
 ([ 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121 ]**[ 184¤106-->107; 185¤107-->108; 186¤107-->109; 187¤109-->110; 188¤110-->106; 189¤110-->109; 190¤110-->111; 191¤110-->112; 192¤109-->110; 193¤109-->107; 194¤107-->113; 195¤107-->114; 196¤115-->116; 197¤116-->115; 198¤116-->117; 199¤116-->118; 200¤115-->116; 201¤115-->119; 202¤119-->106; 203¤119-->115; 204¤119-->120; 205¤119-->121 ],.[ 90; 91; 92; 93; 94; 95; 96; 97; 122; 123; 124; 125; 126; 127; 128; 129 ]**[ 160¤90-->91; 161¤91-->90; 162¤91-->92; 163¤91-->93; 164¤90-->91; 165¤90-->94; 166¤94-->95; 167¤94-->90; 168¤94-->96; 169¤94-->97; 206¤122-->94; 207¤91-->122; 208¤123-->124; 209¤124-->123; 210¤124-->125; 211¤124-->126; 212¤123-->124; 213¤123-->127; 214¤127-->122; 215¤127-->123; 216¤127-->128; 217¤127-->129 ].,[ 218¤171-->122; 219¤171-->90; 220¤171-->123; 221¤171-->95; 222¤154-->127; 223¤124-->154 ]);
 ([ 130; 131; 132; 133; 134; 135; 136; 137 ]**[ 226¤130-->131; 227¤131-->130; 228¤131-->132; 229¤131-->133; 230¤130-->131; 231¤130-->134; 232¤134-->135; 233¤134-->130; 234¤134-->136; 235¤134-->137 ],.[ 138; 139; 140; 141; 142; 143; 144; 145 ]**[ 236¤138-->139; 237¤139-->138; 238¤139-->140; 239¤139-->141; 240¤138-->139; 241¤138-->142; 242¤142-->143; 243¤142-->138; 244¤142-->144; 245¤142-->145 ].,[ 246¤172-->138; 247¤172-->143; 248¤146-->142; 249¤139-->146 ]);
 ([ 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121 ]**[ 184¤106-->107; 185¤107-->108; 186¤107-->109; 187¤109-->110; 188¤110-->106; 189¤110-->109; 190¤110-->111; 191¤110-->112; 192¤109-->110; 193¤109-->107; 194¤107-->113; 195¤107-->114; 196¤115-->116; 197¤116-->115; 198¤116-->117; 199¤116-->118; 200¤115-->116; 201¤115-->119; 202¤119-->106; 203¤119-->115; 204¤119-->120; 205¤119-->121 ],.[ 130; 131; 132; 133; 134; 135; 136; 137; 146; 147; 148; 149; 150; 151; 152; 153 ]**[ 226¤130-->131; 227¤131-->130; 228¤131-->132; 229¤131-->133; 230¤130-->131; 231¤130-->134; 232¤134-->135; 233¤134-->130; 234¤134-->136; 235¤134-->137; 250¤146-->134; 251¤131-->146; 252¤147-->148; 253¤148-->147; 254¤148-->149; 255¤148-->150; 256¤147-->148; 257¤147-->151; 258¤151-->146; 259¤151-->147; 260¤151-->152; 261¤151-->153 ].,[ 262¤173-->146; 263¤173-->130; 264¤173-->147; 265¤173-->135; 266¤154-->151; 267¤148-->154 ]);
 ([ 3; 4; 5; 6; 7; 8; 9; 10 ]**[ 3¤3-->4; 4¤3-->5; 5¤5-->6; 7¤6-->5; 8¤6-->7; 9¤6-->8; 10¤5-->6; 11¤5-->3; 12¤3-->9; 13¤3-->10 ],.[ 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 154; 155; 156; 157; 158; 159; 160; 161 ]**[ 184¤106-->107; 185¤107-->108; 186¤107-->109; 187¤109-->110; 188¤110-->106; 189¤110-->109; 190¤110-->111; 191¤110-->112; 192¤109-->110; 193¤109-->107; 194¤107-->113; 195¤107-->114; 196¤115-->116; 197¤116-->115; 198¤116-->117; 199¤116-->118; 200¤115-->116; 201¤115-->119; 202¤119-->106; 203¤119-->115; 204¤119-->120; 205¤119-->121; 268¤116-->154; 269¤154-->119; 270¤155-->156; 271¤156-->155; 272¤156-->157; 273¤156-->158; 274¤155-->156; 275¤155-->159; 276¤159-->154; 277¤159-->155; 278¤159-->160; 279¤159-->161 ].,[ 280¤2-->159; 281¤1-->115; 282¤1-->106; 283¤1-->154; 284¤1-->108; 285¤1-->155; 286¤1-->109; 287¤156-->2 ]);
 ([ 3; 4; 5; 6; 7; 8; 9; 10 ]**[ 3¤3-->4; 4¤3-->5; 5¤5-->6; 7¤6-->5; 8¤6-->7; 9¤6-->8; 10¤5-->6; 11¤5-->3; 12¤3-->9; 13¤3-->10 ],.[ 162; 163; 164; 165; 166; 167; 168; 169 ]**[ 292¤162-->163; 293¤163-->162; 294¤163-->164; 295¤163-->165; 296¤162-->163; 297¤162-->166; 298¤166-->167; 299¤166-->162; 300¤166-->168; 301¤166-->169 ].,[ 302¤2-->166; 303¤1-->162; 304¤1-->167; 305¤163-->2 ]) ].

Definition variant : Model :=
[ 1; 2; 98; 99; 100; 101; 102; 103; 104; 105; 122; 123; 124; 125; 126; 127; 128; 129; 138; 139; 140; 141; 142; 143; 144; 145; 146; 147; 148; 149; 150; 151; 152; 153; 154; 155; 156; 157; 158; 159; 160; 161; 162; 163; 164; 165; 166; 167; 168; 169 ]**[ 1¤1-->2; 170¤98-->99; 171¤99-->98; 172¤99-->100; 173¤99-->101; 174¤98-->99; 175¤98-->102; 176¤102-->103; 177¤102-->98; 178¤102-->104; 179¤102-->105; 182¤122-->102; 183¤99-->122; 208¤123-->124; 209¤124-->123; 210¤124-->125; 211¤124-->126; 212¤123-->124; 213¤123-->127; 214¤127-->122; 215¤127-->123; 216¤127-->128; 217¤127-->129; 222¤154-->127; 223¤124-->154; 236¤138-->139; 237¤139-->138; 238¤139-->140; 239¤139-->141; 240¤138-->139; 241¤138-->142; 242¤142-->143; 243¤142-->138; 244¤142-->144; 245¤142-->145; 248¤146-->142; 249¤139-->146; 252¤147-->148; 253¤148-->147; 254¤148-->149; 255¤148-->150; 256¤147-->148; 257¤147-->151; 258¤151-->146; 259¤151-->147; 260¤151-->152; 261¤151-->153; 266¤154-->151; 267¤148-->154; 270¤155-->156; 271¤156-->155; 272¤156-->157; 273¤156-->158; 274¤155-->156; 275¤155-->159; 276¤159-->154; 277¤159-->155; 278¤159-->160; 279¤159-->161; 280¤2-->159; 283¤1-->154; 285¤1-->155; 287¤156-->2; 292¤162-->163; 293¤163-->162; 294¤163-->164; 295¤163-->165; 296¤162-->163; 297¤162-->166; 298¤166-->167; 299¤166-->162; 300¤166-->168; 301¤166-->169; 302¤2-->166; 303¤1-->162; 304¤1-->167; 305¤163-->2; 306¤1-->146; 307¤1-->147; 308¤1-->138; 309¤1-->143; 310¤1-->122; 311¤1-->123; 312¤1-->98; 313¤1-->103 ].


Eval compute in FS.SET.bConsistent fss model.

Eval compute in EXE.executeFss fss.
Eval compute in GRAPH.bEqual (EXE.executeFss fss) variant.

Eval compute in MODEL.bConsistent variant model.