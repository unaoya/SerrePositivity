module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelKanCoordinates

/-!
概要：元の模型 Kan 比較の全 path を元の単位上へ制限する。
方針：単位の自然性と指定 Kan path 比較の単位式から、元の底固定円柱を回収する。
規約：全高次単体を保持。使われ方：native 比較候補との指定 path 類の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)
local notation "p" => smallLeftUnstraighteningProjection Z
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight

/-- 単位上の全 path は元の底固定円柱の curry の単位像に厳密に一致する。 -/
lemma coherentCospanConeKanComparison_unit_path :
    continuousKanReplacementUnit.app (smallLeftUnstraightening F) ≫
      (coherentCospanConeKanComparison F X Y Z C ≫
        intervalPullbackPath (continuousKanReplacement.map cf) (continuousKanReplacement.map cg)) =
      curry ((β_ (Δ[1] : SSet.{u}) (smallLeftUnstraightening F)).hom ≫
        (coherentCospanConeRelativePathHomotopy F X Y Z C).h) ≫
          (ihom (Δ[1] : SSet.{u})).map
            (continuousKanReplacementUnit.app (smallLeftUnstraightening Z)) := by
  rw [coherentCospanConeKanComparison_path, ← Category.assoc,
    ← continuousKanReplacementUnit.naturality, Category.assoc,
    fiberwiseIntervalKanComparison_unit, ← Category.assoc]
  dsimp only [Functor.id_map, coherentCospanConeTotalModelPath]
  rw [fiberwiseHomotopyPoint_path]
  rfl

end SerrePositivity.InfinityCategories.F2
