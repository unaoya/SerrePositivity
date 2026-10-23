module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCospanModelKanUnitPath
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPathPrecompCylinder

/-!
概要：元の模型 Kan 比較の全 path を元の二合成の間の円柱として読む。
方針：元の引き戻し円柱を制限し、二脚の厳密な式で両端だけ表示変更する。
規約：同じ全円柱を使用。使われ方：指定 Kan 延長の同型との比較。
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
local notation "cl" => coherentTransformationTotalMap F X C.toLeft
local notation "cr" => coherentTransformationTotalMap F Y C.toRight
local notation "cf" => coherentTransformationTotalMap X Z C.fromLeft
local notation "cg" => coherentTransformationTotalMap Y Z C.fromRight
local notation "m" => coherentCospanConeKanComparison F X Y Z C
local notation "f" => continuousKanReplacement.map cf
local notation "g" => continuousKanReplacement.map cg

/-- 元の Kan 比較の指定 path を元の二合成の Kan 像の間の円柱として表示する。 -/
def coherentCospanConeKanPathHomotopy :
    SSet.Homotopy (continuousKanReplacement.map (cl ≫ cf))
      (continuousKanReplacement.map (cr ≫ cg)) where
  h := (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m).h
  h₀ := (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m).h₀.trans (by
    rw [← Category.assoc, coherentCospanConeKanComparison_left, Functor.map_comp]
    rfl)
  h₁ := (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m).h₁.trans (by
    rw [← Category.assoc, coherentCospanConeKanComparison_right, Functor.map_comp]
    rfl)
  rel := (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m).rel

/-- 元の単位で全円柱を制限すると、元の底固定円柱の単位像そのものである。 -/
lemma coherentCospanConeKanPathHomotopy_unit :
    (continuousKanReplacementUnit.app (smallLeftUnstraightening F) ▷ (Δ[1] : SSet.{u})) ≫
      (coherentCospanConeKanPathHomotopy F X Y Z C).h =
        (coherentCospanConeRelativePathHomotopy F X Y Z C).h ≫
          continuousKanReplacementUnit.app (smallLeftUnstraightening Z) := by
  change (_ ▷ (Δ[1] : SSet.{u})) ≫
    (functorHomotopyPrecomp (intervalPullbackPathHomotopy f g) m).h = _
  rw [intervalPullbackPathHomotopy_precomp_cylinder]
  have hs : (continuousKanReplacementUnit.app (smallLeftUnstraightening F) ▷
      (Δ[1] : SSet.{u})) ≫
        (β_ (continuousKanReplacement.obj (smallLeftUnstraightening F)) Δ[1]).hom =
      (β_ (smallLeftUnstraightening F) Δ[1]).hom ≫
        (Δ[1] ◁ continuousKanReplacementUnit.app (smallLeftUnstraightening F)) := rfl
  rw [← Category.assoc, hs, Category.assoc, ← uncurry_natural_left,
    coherentCospanConeKanComparison_unit_path, uncurry_natural_right, uncurry_curry]
  rw [← Category.assoc, ← Category.assoc, SymmetricCategory.symmetry]
  rfl

end SerrePositivity.InfinityCategories.F2
