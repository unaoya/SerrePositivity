module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.RightClassifiedIndDensityImage

/-!
概要：左 Kan 延長は、元の weighted 全空間上の同じ全密度余錐を余極限へ写す。
方針：元の全空間の密度余錐の像を、同じ right cofinal 比較で制限する。
規約：一般の κ-filtered 保存性を仮定しない。使われ方：各段の密度余極限との比較の全空間側。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]
  {D : SSet.{u + 1}} [Quasicategory D]

local instance : IsKappaFiltered κ (strictRightFibrationColimit F).val.left :=
  strictRightFibrationColimit_isKappaFiltered F

/-- 元の weighted 全空間上の同じ密度余錐の像は、指定左 Kan 延長の native な余極限。 -/
lemma weightedIndDensity_image_isColimit
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    IsColimitCone (mapJoinCocone G (weightedIndDensityCocone κ F)) := by
  have : Quasicategory (CategoryTheory.Limits.colimit (rightFibrationTotalDiagram F)) :=
    quasicategory_of_innerFibration (strictRightFibrationColimitProjection F)
  have hc := rightClassifiedIndDensity_image_isColimit κ β hβ (strictRightFibrationColimit F)
  have hr := (isColimitCone_iff_restrict_rightCofinal _
    (isRightCofinal_ulift _ (strictRightFibrationTotalAssembly_isRightCofinal (κ := κ) F))
    (mapJoinCocone G (rightClassifiedIndDensityCocone κ (strictRightFibrationColimit F)))).mp hc
  unfold weightedIndDensityCocone
  apply (mapJoinCocone_diagramEq_isColimit_iff G _ _).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp hr

end SerrePositivity.InfinityCategories.F2.Ind
