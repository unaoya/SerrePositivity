module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedNerveParameterCoefficient
public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.NerveHornLift
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：固定した底の単体を保って、元の weighted nerve の相対左ホーンを充填する。
方針：最後の係数射影の left fibration 性で充填し、既存の同じ候補図式へ移す。
規約：係数の全空間に Kan 性を要求せず、元の底の射を厳密に保持する。
使われ方：left fibration 値図式の積上の共同 left fibration。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
  (η : F ⟶ (CategoryTheory.Functor.const I).obj B)

/-- 元の係数射影の持ち上げを、同じ底を保つ weighted nerve の充填へ移す。 -/
lemma exists_weightedNerve_parameter_leftHorn_lift {n : ℕ}
    (σ : ComposableArrows I (n + 1)) (k : Fin (n + 2)) (hk : k < Fin.last (n + 1))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (η.app (σ.obj (Fin.last (n + 1))))]
    (a : (horn (n + 1) k : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ B)
    (hb : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η = (horn (n + 1) k).ι ≫ b) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F,
      (horn (n + 1) k).ι ≫ H = a ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = SSet.yonedaEquiv.symm σ ∧
      H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η = b := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := η.app (σ.obj (Fin.last (n + 1)))) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftHornInclusions.intro k hk)
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHornLastCoefficient F σ k a ha)
      (horn (n + 1) k).ι (η.app (σ.obj (Fin.last (n + 1)))) b :=
    ⟨by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveHornLastCoefficient_parameter]; exact hb⟩
  obtain ⟨ψ, hp, ht, hlast⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.SetWeightedTensors.exists_weightedNerveHorn_candidate_with_last_of_coefficient_filler
      F σ k (ne_of_lt hk) a ha sq.lift sq.fac_left
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1) := ⟨σ, ψ⟩
  let H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F := SSet.yonedaEquiv.symm s
  have hface (j : Fin (n + 2)) (hj : j ≠ k) :
      stdSimplex.δ j ≫ H = horn.ι k j hj ≫ a := by
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveHorn_candidate_face_agreement F σ k (ne_of_lt hk)
      a ha ψ hp ht j hj
    calc
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F (SimplexCategory.δ j) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (SimplexCategory.δ j) s
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (horn.ι k j hj ≫ a)) := congrArg _ he
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  refine ⟨H, horn.hom_ext' hface, ?_, ?_⟩
  · rw [SSet.yonedaEquiv_symm_comp]
    rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter_yoneda]
    change ψ.app (Fin.last (n + 1)) ≫ _ = b
    rw [hlast]
    exact sq.fac_right

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
