module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedNerveParameterHorn
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UnderSectionScaffoldBase

/-!
概要：固定底への left fibration 値の strict 図式は、同じ底と添字の積上の left fibration を持つ。
方針：元の積上の左ホーンを二射影へ分け、最後の係数での相対充填を使う。
規約：元の積の単体を保ち、係数の全空間の Kan 性を仮定しない。
使われ方：coherent 前層図式とその strict 分類図式の共同全空間の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の係数射影が left fibration なら、元の積への共同射影も left fibration。 -/
instance weightedNerveParameterProjection_leftFibration
    {I : Type u} [Category.{u} I] {F : I ⥤ SSet.{u}} {B : SSet.{u}}
    (η : F ⟶ (CategoryTheory.Functor.const I).obj B) [∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (η.app i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection η) where
  mem := by
    intro A D j hj
    cases hj with
    | @intro n k hk =>
      constructor
      intro a b sq
      let σ := SSet.yonedaEquiv (b ≫ snd B (nerve I))
      have hσ : SSet.yonedaEquiv.symm σ = b ≫ snd B (nerve I) :=
        SSet.yonedaEquiv.symm_apply_apply _
      have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
          (horn (n + 1) k).ι ≫ SSet.yonedaEquiv.symm σ := by
        have h := congrArg (fun t ↦ t ≫ snd B (nerve I)) sq.w
        simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_snd, hσ] using h
      have hb : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter η =
          (horn (n + 1) k).ι ≫ b ≫ fst B (nerve I) := by
        have h := congrArg (fun t ↦ t ≫ fst B (nerve I)) sq.w
        simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_fst] using h
      obtain ⟨H, hH, hHp, hHb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_weightedNerve_parameter_leftHorn_lift
        η σ k hk a ha (b ≫ fst B (nerve I)) hb
      refine CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := ?_ }
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_fst, hHb]
      · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection, lift_snd, hHp, hσ]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
