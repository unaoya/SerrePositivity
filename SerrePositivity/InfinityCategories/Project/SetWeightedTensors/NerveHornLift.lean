module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveHornFaceAgreement
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveHornCandidateFiller
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：最後の係数値の実際の充填を、元の weighted nerve の相対ホーンの充填へ戻す。
方針：係数の充填から作る図式の全ての面の一致と Yoneda の表示を使う。
規約：係数に Kan 性は要求しない。最後の面を含む相対ホーンを扱う。
使われ方：quasicategory 値 weighted nerve の inner・cocartesian fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

/-- 最後の係数で充填できる相対ホーンは、元の図式を保つ weighted nerve の相対充填を持つ。 -/
lemma exists_weightedNerveHorn_lift_of_coefficient_filler {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C (n + 1))
    (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1))
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (h : ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ F.obj (σ.obj (Fin.last (n + 1))),
      (horn (n + 1) k).ι ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = SSet.yonedaEquiv.symm σ := by
  obtain ⟨H₀, hH₀⟩ := h
  obtain ⟨ψ, hp, ht⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.exists_weightedNerveHorn_candidate_of_coefficient_filler F σ k hk a ha H₀ hH₀
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  let H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F := SSet.yonedaEquiv.symm s
  have hface (j : Fin (n + 2)) (hj : j ≠ k) : stdSimplex.δ j ≫ H = horn.ι k j hj ≫ a := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHorn_candidate_face_agreement F σ k hk a ha ψ hp ht j hj
    calc
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (SimplexCategory.δ j) s
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) :=
        congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm he
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  refine ⟨H, horn.hom_ext' hface, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
