module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.PositivePathShiftIso
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.LeftIntervalWeightedSimplex

/-!
概要：coherent な単体を、正頂点側に元の全 Hom を保つ一つ大きい単体へ移す。
方針：初点と最初の正頂点を同じ頂点へ送る順序写像で前合成し、正頂点の path 同型を使う。
規約：tail の対象と Hom を明示し、Hom の作用やその合成を選び直さない。
使われ方：実際の左区間の対角評価を tail にして、weighted head の係数から cone を組む。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 初点を零へ、各正頂点の i.succ を i へ送る順序写像。 -/
def coherentTailRetraction (n : ℕ) : Fin (n + 2) →o Fin (n + 1) where
  toFun := Fin.cases 0 id
  monotone' := by
    intro a b h
    induction a using Fin.cases with
    | zero => exact Fin.zero_le _
    | succ a =>
      induction b using Fin.cases with
      | zero => simp at h
      | succ b => exact Fin.succ_le_succ_iff.mp h

/-- 正頂点間では、前合成の Hom は元の path の移送の厳密な逆。 -/
lemma coherentTailRetraction_map_positive {n : ℕ} (i j : Fin (n + 1)) :
    (SimplicialThickening.functor (coherentTailRetraction n).uliftMap).map
      (⟨ULift.up i.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.succ⟩ = (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).hom).mp
  rw [Iso.hom_inv_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply CategoryTheory.Functor.ext (fun k => ?_)
  apply SimplicialThickening.Path.ext
  change (fun k : ULift.{u} (Fin (n + 2)) => ULift.up (coherentTailRetraction n k.down)) ''
      ((fun k : ULift.{u} (Fin (n + 1)) => ULift.up k.down.succ) '' (P.obj k).I) =
    (P.obj k).I
  rw [Set.image_image]
  change (fun k => k) '' (P.obj k).I = (P.obj k).I
  exact Set.image_id _

/-- 元の coherent simplex の正頂点側の拡張。 -/
def coherentConeTailExtension {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) : (SimplicialNerve C) _⦋n + 1⦌ :=
  (SimplicialThickening.functor (coherentTailRetraction n).uliftMap).comp SSet A

/-- 正頂点上の対象は、元の同じ添字の対象そのもの。 -/
lemma coherentConeTailExtension_obj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) (i : Fin (n + 1)) :
    (coherentConeTailExtension A).obj ⟨ULift.up i.succ⟩ = A.obj ⟨ULift.up i⟩ := rfl

/-- 正頂点間の Hom は、同じ path の逆移送に続く元の全 Hom の作用。 -/
lemma coherentConeTailExtension_map {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) (i j : Fin (n + 1)) :
    (coherentConeTailExtension A).map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ =
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.pathPositiveShiftIso i j).inv ≫ A.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  change (SimplicialThickening.functor (coherentTailRetraction n).uliftMap).map
    (⟨ULift.up i.succ⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.succ⟩ ≫ A.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ = _
  rw [coherentTailRetraction_map_positive]

/-- 前合成に使った順序写像は、最初の退化の元の頂点写像そのもの。 -/
lemma coherentTailRetraction_eq_sigmaZero (n : ℕ) :
    coherentTailRetraction n = (SimplexCategory.σ (0 : Fin (n + 1))).toOrderHom := by
  apply DFunLike.ext
  intro k
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    change k = (0 : Fin (n + 1)).predAbove k.succ
    exact (Fin.predAbove_succ_of_le _ _ (Fin.zero_le _)).symm

/-- tail の拡張は、元の coherent simplex の最初の退化そのもの。 -/
lemma coherentConeTailExtension_eq_sigmaZero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) :
    coherentConeTailExtension A = (SimplicialNerve C).σ 0 A := by
  rw [coherentConeTailExtension, coherentTailRetraction_eq_sigmaZero]
  rfl

/-- 最初の頂点を除くと、元の coherent simplex 全体を厳密に回収する。 -/
lemma coherentConeTailExtension_tail {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {n : ℕ} (A : (SimplicialNerve C) _⦋n⦌) :
    (SimplicialNerve C).δ 0 (coherentConeTailExtension A) = A := by
  rw [coherentConeTailExtension_eq_sigmaZero]
  exact SSet.δ_comp_σ_self_apply (0 : Fin (n + 1)) A

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
