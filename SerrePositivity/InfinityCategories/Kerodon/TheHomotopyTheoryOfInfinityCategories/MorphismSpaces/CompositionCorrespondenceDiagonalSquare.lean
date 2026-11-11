module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CompositionCorrespondenceDiagonalLift

/-!
概要：合成三角形の対角評価と、同じ外ホーンの制限を厳密に可換にする。
方針：外ホーンの二辺の pushout で、元の対角と指定終域辺を照合する。
規約：元の三角形への射と対角を変更しない。
使われ方：対角評価の外ホーン pullback の可換四角形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

variable {X : SSet.{u}} (x : X _⦋0⦌) {y z : X _⦋0⦌} (g : X.Edge y z)
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondence x g

/-- 同じ元の三角形の外ホーン制限は、同じ対角と終域辺の外ホーン。 -/
lemma compositionCorrespondenceDiagonalSquare :
    pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) ≫
        (pre (horn 2 2).ι).app X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap x g := by
  apply uncurry_injective
  apply (horn₂₂.isPushout.map (tensorRight T)).hom_ext
  · calc
      (horn₂₂.ι₀₂ ▷ T) ≫ uncurry
          (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) ≫
            (pre (horn 2 2).ι).app X) =
          (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g := by
        rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
        rfl
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal_uncurry x g).symm
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap_diagonal x g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g)).symm
  · calc
      (horn₂₂.ι₁₂ ▷ T) ≫ uncurry
          (pullback.fst ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.composableHomHornMap x g) ≫
            (pre (horn 2 2).ι).app X) =
          (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation x g := by
        rw [uncurry_pre_app, ← Category.assoc, ← comp_whiskerRight, horn.ι_ι]
        rfl
      _ = fst (Δ[1] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm g.edge :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceEvaluation_last x g
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cospanHomHornMap_target x g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compositionCorrespondenceDiagonal x g)).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
