module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityRelativeRealization
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientCoconeTransformation

/-!
概要：元の全 weighted 密度変換と同じ両端を持つ任意の全変換を、元の係数図式へ制限する。
方針：元の係数包含で全円柱を制限し、両端だけを元の射影・分類頂点で正規化する。
規約：元の全円柱の同じ制限。使われ方：相対 join の厳密化後の単位を同じ係数余錐へ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v))
  (η : SSet.Homotopy (weightedIndDensitySource κ F)
    (weightedIndDensityIndexProjection F ≫ weightedIndClassification κ F hF)) (i : I)

/-- 元の全変換と同じ両端を持つ全変換の、元の係数図式上の同じ制限。 -/
def weightedIndCoefficientRestriction : SSet.Homotopy (weightedIndCoefficientDiagram κ F i)
    (SSet.const (weightedIndCoefficientVertex κ F hF i)) := by
  let H := functorHomotopyPrecomp η ((SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveConstantLift (rightFibrationTotalDiagram F) i))
  have hs : (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫ weightedIndDensitySource κ F =
        weightedIndCoefficientDiagram κ F i := by
    rw [weightedIndDensitySource, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      weightedDensityProjection_coefficient]
  have ht : (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫
      (weightedIndDensityIndexProjection F ≫ weightedIndClassification κ F hF) =
        SSet.const (weightedIndCoefficientVertex κ F hF i) := by
    rw [weightedIndDensityIndexProjection, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      weightedNerveConstantLift_projection]
    have hu : (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.const (nerveVertex i) : (F.obj i).val.left ⟶ nerve I) =
        SSet.const (ULift.up (nerveVertex i)) := rfl
    rw [hu, SSet.const_comp]
  exact
    { h := H.h
      h₀ := H.h₀.trans hs
      h₁ := H.h₁.trans ht
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro z
        exact False.elim z.1.property }

/-- 元の係数への制限は、元の全変換の同じ全円柱を厳密に保持する。 -/
lemma weightedIndCoefficientRestriction_h : (weightedIndCoefficientRestriction κ F hF η i).h =
    ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷
        (Δ[1] : SSet.{u + 1})) ≫ η.h := rfl

omit η in
/-- 元の全変換に適用すると、元の指定係数変換そのものを回収する。 -/
lemma weightedIndCoefficientRestriction_original :
    weightedIndCoefficientRestriction κ F hF (weightedIndDensityHomotopy κ F hF) i =
      weightedIndDensityCoefficientHomotopy κ F hF i := by
  apply SSet.RelativeMorphism.Homotopy.ext
  rfl

end SerrePositivity.InfinityCategories.F2.Ind
