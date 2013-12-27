(* tested with Coq 8.4 *)

(* Copyright 2012, Ralph Matthes and Celia Picard, IRIT, CNRS & Université de Toulouse *)

Set Implicit Arguments.
Require Import Utf8. (* just for displaying purposes *)
Require Import Streams. (* this hides hd of List *)
Require Import Setoid.

Require Import Relations.
Require Import Morphisms.

Module Type Elt.

  Parameter Inline(10) E : Type.

End Elt.

Module TriangleMP (Import TE : Elt).

  Open Scope type_scope. (* asterisk is interpreted as product of types *)

  (** the datatype of triangles *)

  CoInductive Tri (A: Type): Type :=
    constr: A -> Tri(E * A) -> Tri A.

  (** the datatype of trapeziums *)

  Definition Trap (A: Type) := Tri(E * A).

  Check constr: forall A: Type, A -> Trap A -> Tri A.

  Definition top (A: Type) (t: Tri A): A :=
    match t with constr a _ => a end.

  Definition rest (A: Type) (t: Tri A): Trap A :=
    match t with constr _ r => r end.

  Lemma toprestOK (A: Type) (t: Tri A):
    t = constr (top t) (rest t).
  Proof.
    destruct t as [a r].
    reflexivity.
  Qed.

  (** cutting off the top row *)

  CoFixpoint cut (A: Type) (t: Trap A): Tri A := match t with constr (e, a) r => constr a (cut r) end.

  Lemma cut_top (A: Type) (t: Trap A): top(cut t) = snd(top t).
  Proof.
    destruct t as [[e a] r].
    reflexivity.
  Qed.

  Lemma cut_rest  (A: Type) (t: Trap A): rest(cut t) = cut(rest t).
  Proof.
    destruct t as [[e a] r].
    reflexivity.
  Qed.

  Lemma cut_OK (A: Type)(ea: E * A)(r: Trap(E * A)): cut (constr ea r) = constr (snd ea) (cut r).
  Proof.
    destruct ea as [e a].
    rewrite (toprestOK (cut (constr (e, a) r))).
    reflexivity.
  Qed.

  Lemma cut_OK_eager (A: Type) (t: Trap A): cut t = constr (snd (top t)) (cut (rest t)).
  Proof.
    destruct t as [ea r].
    apply cut_OK.
  Qed.

  (** lifting a redecoration rule from triangles to trapeziums *)

  Definition lift (A B: Type) (f: Tri A -> B) (r: Trap A) : E * B := (fst(top r), f(cut r)).

  (* pattern-matching version - not ideal for computation
CoFixpoint redec (A B: Type) (f: Tri A -> B) (t: Tri A): Tri B :=
  match t with
    constr a r => constr (f t) (redec (lift f) r)
  end.
   *)

  (** the short and elegant definition with the nested datatype *)
  CoFixpoint redec (A B: Type) (f: Tri A -> B) (t: Tri A): Tri B :=
    constr (f t) (redec (lift f) (rest t)).

  Lemma comonad1 (A B: Type) (f: Tri A -> B) (t: Tri A): top(redec f t) = f t.
  Proof.
    reflexivity.
  Qed.

  Lemma redec_rest (A B: Type) (f: Tri A -> B) (t: Tri A):
    rest(redec f t) = redec (lift f) (rest t).
  Proof.
    reflexivity.
  Qed.

  Lemma redec_OK (A B: Type) (f: Tri A -> B) (a: A) (r: Trap A): redec f (constr a r) =
                                                                constr (f (constr a r)) (redec (lift f) r).
  Proof.
    rewrite (toprestOK (redec f (constr a r))).
    reflexivity.
  Qed.


  (** printing ~~ %\ensuremath{\simeq}% *)
  (** printing t' %\ensuremath{t'}% *)

  (* the canonical notion of bisimilarity on Tri *)

  CoInductive bisimilar: forall A, Tri A -> Tri A -> Prop :=
    constrB: forall (A: Type)(t t': Tri A),
               top t = top t' -> bisimilar (rest t) (rest t') -> bisimilar t t'.
  (* begin hide *)
  Infix "~~" := bisimilar (at level 60).
  (* end hide *)

  (** The relation [bisimilar] is displayed as the infix $\simeq$#~~#. *)
  (** printing a' %\ensuremath{a'}% *)

  (* what cut exactly cuts out *)

  CoFixpoint es_cut (A: Type) (t: Trap A): Stream E :=
    match t with
        constr (e, a) r => Cons e (es_cut r)
    end.

  CoFixpoint add_es (A: Type)(es: Stream E)(t: Tri A): Trap A :=
    match es, t with
        Cons e es', constr a r => constr (e, a) (add_es es' r)
    end.

  (* already the following lemma cannot be expected to hold with Leibniz equality *)

  Lemma es_cut_reconstr (A: Type)(t: Trap A): add_es (es_cut t) (cut t) ~~ t.
  Proof.
    revert A t ; cofix Hc ; intros A [[e a] r].
    apply constrB.
    reflexivity.
    simpl.
    apply Hc.
  Qed.

  Lemma cut_add_es (A: Type)(es: Stream E)(t: Tri A): cut (add_es es t) ~~ t.
  Proof.
    revert A es t; cofix Hc; intros A [e es] [a r].
    apply constrB; simpl.
    reflexivity.
    apply Hc.
  Qed.

  (* inversion lemmas for constrB *)

  Lemma bisimilar_injr (A: Type) (a a': A) (t t': Trap A):
    constr a t ~~ constr a' t' -> t ~~ t'.
  Proof.
    intros H.
    refine (match H in (t ~~ t')  return (rest t ~~ rest t') with
                constrB t t' Hyp1 Hyp2  => _ end).
    assumption.
  Qed.

  Lemma bisimilar_injl (A: Type) (a a': A) (t t': Trap A):
    constr a t ~~ constr a' t' -> a = a'.
  Proof.
    intros H.
    refine (match H in (t ~~ t') return (top t = top t') with
                constrB t t' Hyp1 Hyp2  => _ end).
    assumption.
  Qed.

  (* bisimilarity is an equivalence relation *)

  Lemma bisimilar_refl : forall (A: Type), Reflexive (@bisimilar A).
  Proof.
    cofix Hc.
    intros A [t r].
    apply constrB;
      reflexivity.
  Qed.

  (** printing t1 %\ensuremath{t_1}% *)
  (** printing t2 %\ensuremath{t_2}% *)
  (** printing t3 %\ensuremath{t_3}% *)

  Lemma bisimilar_sym : forall (A: Type), Symmetric (@bisimilar A).
  Proof.
    cofix Hc.
    intros A [t1 r1] [t2 r2] H.
    apply constrB; simpl.
    rewrite (bisimilar_injl H).
    reflexivity.
    symmetry.
    apply (bisimilar_injr H).
  Qed.

  Lemma bisimilar_trans : forall (A: Type), Transitive (@bisimilar A).
  Proof.
    cofix Hc.
    intros A [t1 r1] [t2 r2] [t3 r3] H1 H2.
    apply constrB; simpl.
    rewrite (bisimilar_injl H1), (bisimilar_injl H2).
    reflexivity.
    transitivity r2.
    apply (bisimilar_injr H1).
    apply (bisimilar_injr H2).
  Qed.

  Add Parametric Relation (A: Type): (Tri A) (bisimilar(A:= A))
      reflexivity proved by (bisimilar_refl(A:= A))
      symmetry proved by (bisimilar_sym(A:= A))
      transitivity proved by (bisimilar_trans(A:= A))
        as bisimilarRel.

  (** printing ==> %\ensuremath{\Longrightarrow}% *)

  Lemma top_cong (A: Type) (t1 t2: Tri A): t1 ~~ t2 -> top t1 = top t2.
  Proof.
    intros H.
    destruct t1 as [t1 r1] ; destruct t2 as [t2 r2].
    rewrite (bisimilar_injl H).
    reflexivity.
  Qed.

  Add Parametric Morphism (A: Type): (top(A:= A))
      with signature (bisimilar(A:= A)) ==> (eq(A:= A))
        as topM.
  Proof.
    exact (top_cong(A:= A)).
  Qed.

  Lemma rest_cong (A: Type) (t1 t2: Tri A): t1 ~~ t2 -> rest t1 ~~ rest t2.
  Proof.
    intros H.
    destruct t1 as [t1 r1] ; destruct t2 as [t2 r2].
    apply bisimilar_injr in H.
    assumption.
  Qed.

  Add Parametric Morphism (A: Type): (rest(A:= A))
      with signature (bisimilar(A:= A)) ==> (bisimilar(A:= E * A))
        as restM.
  Proof.
    exact (rest_cong(A:= A)).
  Qed.

  Lemma cut_cong : forall (A: Type)(t t': Trap A), t ~~ t' -> cut t ~~ cut t'.
  Proof.
    cofix Hc.
    intros A [[e a] r] [[e' a'] r'] H.
    apply constrB; simpl.
    apply bisimilar_injl in H.
    inversion H ; reflexivity.
    apply Hc.
    apply (bisimilar_injr H).
  Qed.

  Add Parametric Morphism (A: Type): (cut(A:= A))
      with signature (bisimilar(A:= E * A)) ==> (bisimilar(A:= A))
        as cutM.
  Proof.
    exact (cut_cong(A:= A)).
  Qed.

  Lemma add_es_cong (A: Type)(es: Stream E)(t1 t2: Tri A): t1 ~~ t2 -> add_es es t1 ~~ add_es es t2.
  Proof.
    revert A es t1 t2.
    cofix Hc; intros.
    destruct t1 as [a1 r1]; destruct t2 as [a2 r2].
    destruct es as [e es'].
    apply constrB; simpl.
    rewrite (bisimilar_injl H).
    reflexivity.
    apply Hc.
    apply (bisimilar_injr H).
  Qed.

  Add Parametric Morphism (A: Type)(es: Stream E): (add_es es)
      with signature (bisimilar(A:= A)) ==> (bisimilar(A:= E * A))
        as add_esM.
  Proof.
    intros.
    apply add_es_cong.
    assumption.
  Qed.

  (** printing f' %\ensuremath{f'}% *)

  Definition fequiv (A B: Type) (f f': A -> B): Prop := forall t: A, f t = f' t.
  (* begin hide *)
  Infix "=e" := fequiv (at level 60).
  (* end hide *)

  Lemma fequiv_refl (A B: Type): Reflexive (@fequiv A B).
  Proof.
    do 2 red; intros; reflexivity.
  Qed.

  Lemma fequiv_sym (A B: Type): Symmetric (@fequiv A B).
  Proof.
    do 2 red; intros; symmetry; apply H.
  Qed.

  Lemma fequiv_trans (A B: Type): Transitive (@fequiv A B).
  Proof.
    do 2 red; intros f g h H1 H2 a.
    transitivity (g a); (apply H1 || apply H2).
  Qed.

  Add Parametric Relation (A B: Type): (A -> B) (@fequiv A B)
      reflexivity proved by (fequiv_refl(A:= A)(B:= B))
      symmetry proved by (fequiv_sym(A:= A)(B:= B))
      transitivity proved by (fequiv_trans(A:= A)(B:= B))
        as fequivRel.

  Lemma lift_ext : forall (A B: Type) (f f': Tri A -> B), f =e f' -> lift f =e lift f'.
  Proof.
    intros A B f f' H [ea r].
    unfold lift.
    rewrite H.
    reflexivity.
  Qed.

  (** redec only depends on the extension of its functional argument *)

  Lemma redec_ext : forall (A B: Type) (f f': Tri A -> B) (t: Tri A), f =e f' -> redec f t ~~ redec f' t.
  Proof.
    cofix Hc.
    intros A B f f' [t r] H.
    apply constrB; simpl.
    apply H.
    apply Hc.
    apply lift_ext.
    assumption.
  Qed.

  Definition fcompat (A B: Type)(f: Tri A -> B): Prop := forall (t t': Tri A), t ~~ t' -> f t = f t'.

  Ltac fcompat2Proper f Hf := change (Morphisms.Proper (@bisimilar _ ==> @eq _) f) in Hf.

  Lemma lift_cong (A B: Type)(f: Tri A -> B): fcompat f -> fcompat (lift f).
  Proof.
    red.
    intros Hf [ea r] [ea' r'] Hyp.
    apply injective_projections; simpl.
    apply bisimilar_injl in Hyp.
    rewrite Hyp.
    reflexivity.
    apply Hf.
    apply cut_cong.
    assumption.
  Qed.

  (* a preparation for the second comonad law *)

  Lemma lift_top (A: Type): lift (top(A:= A)) =e top(A:= E * A).
  Proof.
    intros [[e a] r].
    reflexivity.
  Qed.

  (* a stronger statement to get the proof through *)

  Lemma comonad2_stronger (A: Type)(f: Tri A -> A)(Hf: f =e top(A:= A))(t: Tri A): redec f t ~~ t.
  Proof.
    revert A f Hf t.
    cofix Hc.
    intros A f Hf [a r].
    apply constrB.
    simpl.
    rewrite Hf.
    reflexivity.
    simpl.
    apply Hc.
    clear a r.
    rewrite <- lift_top.
    apply lift_ext.
    assumption.
  Qed.

  Corollary comonad2 (A: Type) (t: Tri A): redec (top(A:= A)) t ~~ t.
  Proof.
    apply comonad2_stronger.
    reflexivity.
  Qed.

  (* preparations for the third comonad law *)

  Lemma redec_cut: forall (A B: Type) (f: Tri A -> B) (r: Trap A),
                     redec f (cut r) ~~ cut(redec (lift f) r).
  Proof.
    cofix Hc.
    intros A B f [[e a] t].
    apply constrB; simpl.
    reflexivity.
    apply Hc.
  Qed.

  (** composition *)
  (** printing o %\ensuremath{\circ}% *)
  Definition comp (A B C: Type) (g: B -> C) (f: A -> B): A -> C := fun x => g (f x).
  (* begin hide *)
  Infix "o" := comp (at level 90).
  (* end hide *)

  (** [comp] is displayed as the infix $\circ$#o#. *)

  Lemma auxcomonad3 (A B C: Type) (f: Tri A -> B) (g: Tri B -> C)(Hg: fcompat g):
    lift (g o redec f) =e (lift g o redec (lift f)).
  Proof.
    intro r.
    unfold comp.
    unfold lift at 1 2.
    rewrite comonad1.
    apply injective_projections; simpl.
    reflexivity.
    apply Hg, redec_cut.
  Qed.

  (* a stronger statement to get the proof through *)

  Lemma comonad3_stronger (A B C: Type)(f: Tri A -> B)(g: Tri B -> C)(Hg : fcompat g)(h: Tri A -> C)
        (Hh: h =e (g  o (redec f)))(t: Tri A): redec h t ~~ redec g (redec f t).
  Proof.
    revert A B C f g Hg h Hh t.
    cofix Hc.
    intros A B C f g Hg h Hh [a r].
    apply constrB.
    simpl.
    rewrite Hh.
    reflexivity.
    simpl.
    apply Hc.
    apply lift_cong.
    assumption.
    clear a r.
    rewrite <- (auxcomonad3 f (g:= g)); try assumption.
    apply lift_ext.
    assumption.
  Qed.

  Corollary comonad3 (A B C: Type) (f: Tri A -> B) (g: Tri B -> C) (t: Tri A):
    fcompat g -> redec (g o redec f) t ~~ redec g (redec f t).
  Proof.
    intro Hg.
    apply (comonad3_stronger f Hg); reflexivity.
  Qed.

  (* a preliminary version without type classes:
Definition fcompatGen (T: Type -> Type)(equiv: forall A: Type, relation (T A))(A B: Type)(f: T A -> B): Prop :=
  forall (t t': T A), equiv _ t t' -> f t = f t'.
   *)

  Class Equiv (T: Type -> Type) := equiv : forall {A: Type}, relation (T A).
  Infix "~~^" := equiv (at level 70):type_scope.

  Definition fcompatGen (T: Type -> Type)(E_eq: Equiv T)(A B: Type)(f: T A -> B): Prop :=
    forall (t t': T A), t ~~^ t' -> f t = f t'.

  Lemma fcompatGenProper (T: Type -> Type)(E_eq: Equiv T)(A B: Type)(f: T A -> B):
    fcompatGen E_eq A f = Proper (E_eq A ==> eq) f.
  Proof.
    reflexivity.
  Qed.

  Class WeakComonad (T: Type -> Type)(E_eq: Equiv T) :=
    {wcounit: forall A: Type, T A -> A; wcobind: forall (A B: Type), (T A -> B) -> T A -> T B;
     wcomonad1gen: forall (A B: Type)(f: T A -> B)(t: T A), wcounit (wcobind f t) = f t;
     wcomonad2gen: forall (A: Type)(t: T A), wcobind (wcounit(A:= A)) t ~~^ t;
     wcomonad3gen: forall (A B C: Type)(f: T A -> B)(g: T B -> C)(t: T A),
                     Proper (E_eq B ==> eq) g -> wcobind (g o wcobind f) t ~~^ wcobind g (wcobind f t)}.

  Program Instance TriComonad: WeakComonad(T:= Tri) bisimilar.
  Next Obligation.
    exact (top X).
  Defined.
  Next Obligation.
    exact (redec X X0).
  Defined.
  Next Obligation.
    apply comonad2.
  Qed.
  Next Obligation.
    apply comonad3.
    assumption.
  Qed.

End TriangleMP.
