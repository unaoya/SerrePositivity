module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementHornSources
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
概要：Kan 係数の simplicial replacement の相対零番目ホーンの充填。
方針：全ての指定面の係数を始点の値に揃えて充填し、元の底の射列と組み直す。
規約：係数図式の構造射の持ち上げ性はこのホーンには要求しない。
使われ方：Kerodon §5.3.5（Tag 037H）、有限順序上の strict transport の全空間比較の充填。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：始点の係数値が Kan なら simplicial replacement の相対零番目ホーンは充填できる。
方針：指定した面の係数の整合性を使い、Kan 値の充填を底の射列と組にして戻す。
規約：底の圏の射に単射性や全ホーン持ち上げ性を要求しない。
使われ方：Kerodon §5.3.5（Tag 037H）、simplicial replacement の初期ホーンの相対充填。 -/
lemma exists_simplicialReplacement_zeroHorn_lift
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {n : ℕ}
    (σ : ComposableArrows C (n + 1)) [KanComplex (F.obj (σ.obj 0))]
    (a : (horn (n + 1) 0 : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F)
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) 0).ι ≫ SSet.yonedaEquiv.symm σ) :
    ∃ H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F,
      (horn (n + 1) 0).ι ≫ H = a ∧
        H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F = SSet.yonedaEquiv.symm σ := by
  obtain ⟨τ, hτ⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementHornSourceFace_zero_isCompatible F σ a ha).exists_lift_of_kanComplex
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex F (n + 1) := ⟨σ, τ⟩
  have hs0 : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSourceCoefficient F s (σ.obj 0) rfl = τ := by
    change τ ≫ F.map (𝟙 (σ.obj 0)) = τ
    rw [F.map_id, Category.comp_id]
  let H : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F := SSet.yonedaEquiv.symm s
  have hface (j : Fin (n + 2)) (hj : j ≠ 0) :
      stdSimplex.δ j ≫ H = horn.ι 0 j hj ≫ a := by
    have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F (SimplexCategory.δ j) s =
        SSet.yonedaEquiv (horn.ι 0 j hj ≫ a) := by
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex_eq_of_sourceCoefficient F _ _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementHornFace_base F σ 0 a ha j hj).symm (σ.obj 0)
        (congrArg σ.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_zero_of_ne_zero j hj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementHornFace_start F σ 0 a ha j hj hj) ?_
      calc
        _ = stdSimplex.δ j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSourceCoefficient F s (σ.obj 0) rfl :=
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSourceCoefficient_naturality F (SimplexCategory.δ j)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFace_zero_of_ne_zero j hj) s (σ.obj 0) rfl _
        _ = stdSimplex.δ j ≫ τ := congrArg (fun f ↦ stdSimplex.δ j ≫ f) hs0
        _ = _ := hτ j hj
    calc
      _ = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap F (SimplexCategory.δ j) s) :=
        SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) (SimplexCategory.δ j) s
      _ = SSet.yonedaEquiv.symm (SSet.yonedaEquiv (horn.ι 0 j hj ≫ a)) :=
        congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) (n := ⦋n⦌)).symm hs
      _ = _ := SSet.yonedaEquiv.symm_apply_apply _
  refine ⟨H, horn.hom_ext' hface, ?_⟩
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

/-- 概要：Kan 値図式の simplicial replacement の射影は零番目ホーンを全次元で持ち上げる。
方針：下の標準単体を底の射列として表示し、始点の係数の充填を適用する。
規約：まだ零番目以外のホーンの持ち上げを主張しない。
使われ方：Kerodon §5.3.5（Tag 037H）、scaffold の補助模型での初期ホーンの持ち上げ。 -/
lemma hasLiftingProperty_simplicialReplacementProjection_zeroHorn
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] (n : ℕ) :
    HasLiftingProperty (horn (n + 1) 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) := by
  constructor
  intro a b sq
  let σ := SSet.yonedaEquiv b
  have hb : SSet.yonedaEquiv.symm σ = b := SSet.yonedaEquiv.symm_apply_apply _
  have ha : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      (horn (n + 1) 0).ι ≫ SSet.yonedaEquiv.symm σ := by
    rw [hb]
    exact sq.w
  obtain ⟨H, hH, hHp⟩ := exists_simplicialReplacement_zeroHorn_lift F σ a ha
  exact CommSq.HasLift.mk' { l := H, fac_left := hH, fac_right := hHp.trans hb }

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
