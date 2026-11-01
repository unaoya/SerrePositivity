module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityDiagramHomotopy
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndClassification
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexHomotopyLift

/-!
概要：元の weighted 密度変換の同じ全円柱を、元の Indκ 内へ持ち上げる。
方針：元の Yoneda と共同分類の包含公式で両端を揃え、既存の全部分圏の厳密な持ち上げを使う。
規約：包含後は元の全変換そのもの。使われ方：大域余極限族の右制限との全比較。
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
local notation "a" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedDensityProjection F)
local notation "q" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedNerveProjection (rightFibrationTotalDiagram F))

/-- 元の全変換を、Indκ 内の元の両図式の包含上で型を揃えて読む。 -/
def weightedIndDensityAmbientHomotopy :
    SSet.Homotopy ((a ≫ indYoneda κ C) ≫ indInclusionPresheaf κ C)
      ((q ≫ weightedIndClassification κ F hF) ≫ indInclusionPresheaf κ C) :=
  let H := weightedDensityDiagramHomotopy F
  { h := H.h
    h₀ := H.h₀.trans (by rw [Category.assoc, indYoneda_inclusion]; rfl)
    h₁ := H.h₁.trans (by rw [Category.assoc, weightedIndClassification_inclusion]; rfl)
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro z
      exact False.elim z.1.property }

/-- 元の全 weighted 密度図式から、元の添字に沿う共同分類への Indκ 内の一つの変換。 -/
def weightedIndDensityHomotopy :
    SSet.Homotopy (a ≫ indYoneda κ C) (q ≫ weightedIndClassification κ F hF) :=
  fullSubcomplexHomotopyLift (IsIndVertex κ C) (a ≫ indYoneda κ C)
    (q ≫ weightedIndClassification κ F hF) (weightedIndDensityAmbientHomotopy κ F hF)

/-- 包含後の同じ全円柱は、元の共同評価から実現した元の密度変換に厳密に一致する。 -/
lemma weightedIndDensityHomotopy_inclusion :
    (weightedIndDensityHomotopy κ F hF).h ≫ indInclusionPresheaf κ C =
      (weightedDensityDiagramHomotopy F).h :=
  fullSubcomplexHomotopyLift_ι (IsIndVertex κ C) _ _ _

end SerrePositivity.InfinityCategories.F2.Ind
