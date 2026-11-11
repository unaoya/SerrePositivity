module

public import SerrePositivity.EInfinity.Hammock.WeakUnionGluing
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# 交わりを保つ元の部分複体族の有限和の弱同値

概要：交わりに閉じた部分複体族の各比較が弱同値なら、任意の有限和の比較も弱同値。
方針：有限和に関する帰納と二つの和の貼り合わせを、交わりで制限した族にも適用する。
規約：元の全体の射による制限を扱い、全体の弱同値性は仮定しない。
使われ方：proper 図式の境界の有限な像の和。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma mapsToSubcomplexFinsetSup {I : Type v} (s : Finset I)
    {A : I → X.Subcomplex} {B : I → Y.Subcomplex}
    (h : ∀ i k, Set.MapsTo (f.app k) ((A i).obj k) ((B i).obj k)) :
    ∀ k, Set.MapsTo (f.app k) ((s.sup A).obj k) ((s.sup B).obj k) := by
  intro k x hx
  simp only [Finset.sup_eq_iSup, Subfunctor.iSup_obj, Set.mem_iUnion] at hx ⊢
  obtain ⟨i, hi, hx⟩ := hx
  exact ⟨i, hi, h i k hx⟩

lemma weakMapSubcomplex_of_eq {A C : X.Subcomplex} {B D : Y.Subcomplex}
    (hAC : A = C) (hBD : B = D)
    (hAB : ∀ k, Set.MapsTo (f.app k) (A.obj k) (B.obj k))
    (hCD : ∀ k, Set.MapsTo (f.app k) (C.obj k) (D.obj k))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f hAB)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f hCD) := by
  cases hAC
  cases hBD
  exact h

lemma weakMapSubcomplex_bottom : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
    (mapSubcomplex f (A := ⊥) (B := ⊥) (fun _ _ hx => False.elim hx)) := by
  have : IsIso (mapSubcomplex f (A := ⊥) (B := ⊥) (fun _ _ hx => False.elim hx)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro k
    rw [CategoryTheory.isIso_iff_bijective]
    constructor
    · intro x
      exact False.elim x.property
    · intro x
      exact False.elim x.property
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (asIso
    (mapSubcomplex f (A := ⊥) (B := ⊥) (fun _ _ hx => False.elim hx)))).isWeakHomotopyEquivalence

lemma subcomplex_inf_finsetSup {I : Type v} (A : I → X.Subcomplex) (s : Finset I)
    (B : X.Subcomplex) : B ⊓ s.sup A = s.sup (fun i => B ⊓ A i) := by
  ext k x
  simp only [Finset.sup_eq_iSup, Subfunctor.min_obj, Subfunctor.iSup_obj,
    Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hB, i, hi, hx⟩
    exact ⟨i, hi, hB, hx⟩
  · rintro ⟨i, hi, hB, hx⟩
    exact ⟨hB, i, hi, hx⟩

lemma weakFiniteUnion {I : Type v} [SemilatticeInf I] (s : Finset I) :
    ∀ (A : I → X.Subcomplex) (B : I → Y.Subcomplex)
      (_hA : ∀ i j, A (i ⊓ j) = A i ⊓ A j) (_hB : ∀ i j, B (i ⊓ j) = B i ⊓ B j)
      (hm : ∀ i k, Set.MapsTo (f.app k) ((A i).obj k) ((B i).obj k)),
      (∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f (hm i))) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (mapSubcomplex f (mapsToSubcomplexFinsetSup f s hm)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro A B hA hB hm hw
    exact weakMapSubcomplex_bottom f
  | @insert i s hi ih =>
    intro A B hA hB hm hw
    have hs := ih A B hA hB hm hw
    have hsi := ih (fun j => A i ⊓ A j) (fun j => B i ⊓ B j)
      (fun j k => by rw [hA]; simp only [inf_assoc, inf_left_comm, inf_left_idem])
      (fun j k => by rw [hB]; simp only [inf_assoc, inf_left_comm, inf_left_idem])
      (fun j => mapsToSubcomplexInf f (hm i) (hm j))
      (fun j => weakMapSubcomplex_of_eq f (hA i j) (hB i j) _ _ (hw (i ⊓ j)))
    have hInt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
        (mapSubcomplex f (mapsToSubcomplexInf f (hm i) (mapsToSubcomplexFinsetSup f s hm))) := by
      exact weakMapSubcomplex_of_eq f (subcomplex_inf_finsetSup A s (A i)).symm
        (subcomplex_inf_finsetSup B s (B i)).symm _ _ hsi
    exact weakMapSubcomplex_of_eq f (by rw [Finset.sup_insert]) (by rw [Finset.sup_insert]) _ _
      (weakUnion_gluing f (hm i) (mapsToSubcomplexFinsetSup f s hm) hInt (hw i) hs)

end SerrePositivity.EInfinity.Hammock
