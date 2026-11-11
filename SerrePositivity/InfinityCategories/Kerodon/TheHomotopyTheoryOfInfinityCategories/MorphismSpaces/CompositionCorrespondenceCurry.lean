module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceFaces

/-!
概要：元の第一辺の族と指定第二辺を持つ三角形を、同じ合成三角形空間へ戻す。
方針：二つの辺の等式を内ホーン全体へ貼り、定義した pullback へ持ち上げる。
規約：元の三角形と第一辺の全パラメーターを厳密に保持する。
使われ方：指定対角と終域辺から、合成三角形空間の族を復元する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X T : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
variable (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y) (H : (Δ[2] : SSet.{u}) ⊗ T ⟶ X)
variable (h₀ : (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry a)
variable (h₁ : (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H =
  fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge)
include h₀ h₁

/-- 同じ二辺の等式は、元の内ホーン全体の等式を与える。 -/
lemma compositionCorrespondenceCurry_horn :
    ((horn 2 1).ι ▷ T) ≫ H = uncurry (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) := by
  apply (horn₂₁.isPushout.map (tensorRight T)).hom_ext
  · calc
      (horn₂₁.ι₀₁ ▷ T) ≫ ((horn 2 1).ι ▷ T) ≫ H =
          (stdSimplex.δ (2 : Fin 3) ▷ T) ≫ H := by
        rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
      _ = _ := h₀
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_first x g a).symm
  · calc
      (horn₂₁.ι₁₂ ▷ T) ≫ ((horn 2 1).ι ▷ T) ≫ H =
          (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ H := by
        rw [← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
      _ = _ := h₁
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap_last x g a).symm

/-- 元の第一辺と三角形を、同じ合成三角形空間の族として束ねる。 -/
def compositionCorrespondenceCurry : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g :=
  pullback.lift (curry H) a (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry]
    exact compositionCorrespondenceCurry_horn x g a H h₀ h₁)

/-- 同じ curry の三角形は、元の三角形を回収する。 -/
lemma compositionCorrespondenceCurry_triangle :
    compositionCorrespondenceCurry x g a H h₀ h₁ ≫
        pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) = curry H :=
  pullback.lift_fst _ _ _

/-- 同じ curry の第一辺は、元の第一辺の族そのもの。 -/
lemma compositionCorrespondenceCurry_first :
    compositionCorrespondenceCurry x g a H h₀ h₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceFirst x g = a :=
  pullback.lift_snd _ _ _

/-- 同じ curry の三角形の評価は、元の全パラメーターの三角形。 -/
lemma compositionCorrespondenceCurry_evaluation :
    (Δ[2] ◁ compositionCorrespondenceCurry x g a H h₀ h₁) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g = H := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation
  rw [← uncurry_natural_left, compositionCorrespondenceCurry_triangle, uncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
