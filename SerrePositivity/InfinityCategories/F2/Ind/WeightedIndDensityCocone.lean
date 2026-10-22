module

public import SerrePositivity.InfinityCategories.F2.Ind.RightClassifiedIndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedTotalAssemblyCofinal
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：strict 図式の元の weighted 全空間上で、同じ分類余極限を頂点とする Indκ 密度余錐。
方針：元の全空間の密度余錐を、証明済みの同じ right cofinal 比較で制限する。
規約：元の底への射影と全余錐を保持。使われ方：各段の密度余極限との Kan 合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

local instance : IsKappaFiltered κ (strictRightFibrationColimit F).val.left :=
  strictRightFibrationColimit_isKappaFiltered F

/-- 元の weighted 全空間から、同じ各段の射影で定める元の底への射。 -/
def weightedIndDensityBase : weightedNerve (rightFibrationTotalDiagram F) ⟶ C :=
  weightedNerveMap (rightFibrationProjectionCocone F).ι ≫ weightedNerveConstantEvaluation I C

/-- 元の weighted 全空間上の、同じ元の射影による表現可能図式。 -/
def weightedIndDensityDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (rightFibrationTotalDiagram F)) ⟶
      IndInfinity κ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedIndDensityBase F) ≫ indYoneda κ C

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] [∀ i, IsKappaFiltered κ (F.obj i).val.left] in
/-- 元の全空間比較による密度図式の制限は、元の weighted 底射影を厳密に回収する。 -/
lemma weightedIndDensity_diagram :
    (SSet.uliftFunctor.{u + 1, u}).map (strictRightFibrationTotalAssembly F) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map (strictRightFibrationColimitProjection F) ≫ indYoneda κ C) =
        weightedIndDensityDiagram κ F := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    strictRightFibrationTotalAssembly_projection]
  rfl

/-- 元の weighted 全空間を添字とする、同じ分類余極限の全密度余錐。 -/
def weightedIndDensityCocone : JoinCocone (weightedIndDensityDiagram κ F) :=
  coherentCoconeOfDiagramEq (weightedIndDensity_diagram κ F)
    ((rightClassifiedIndDensityCocone κ (strictRightFibrationColimit F)).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (strictRightFibrationTotalAssembly F)))

/-- 同じ全密度余錐の頂点は、元の全空間余極限の元の分類値。 -/
lemma weightedIndDensityCocone_vertex :
    (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌) (weightedIndDensityCocone κ F).vertex =
      functorVertex (rightStraighteningPresheafDiagram (strictRightFibrationColimit F)) := by
  rw [weightedIndDensityCocone, coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  exact rightClassifiedIndDensityCocone_vertex κ _

/-- 元の weighted 全空間上の同じ全密度余錐は native な余極限。 -/
lemma weightedIndDensityCocone_isColimit : IsColimitCone (weightedIndDensityCocone κ F) := by
  have : Quasicategory (CategoryTheory.Limits.colimit (rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (strictRightFibrationColimitProjection F)
  apply (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
  exact (isColimitCone_iff_restrict_rightCofinal _
    (isRightCofinal_ulift _ (strictRightFibrationTotalAssembly_isRightCofinal (κ := κ) F)) _).mp
      (rightClassifiedIndDensityCocone_isColimit κ (strictRightFibrationColimit F))

end SerrePositivity.InfinityCategories.F2.Ind
