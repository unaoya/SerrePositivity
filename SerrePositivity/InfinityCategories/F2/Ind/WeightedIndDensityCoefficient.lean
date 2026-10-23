module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedConstantNaturality
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.HomotopyCoconeRealization

/-!
概要：同じ全 weighted 密度変換を、元の各段の全空間上の同じ native 余錐へ実現する。
方針：元の係数包含で全変換を制限し、両端固定の余錐実現を適用する。
規約：余極限性は別工程。使われ方：指定変換の元の fiber の密度余錐との全比較。
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
      (Opposite.op ⦋0⦌) v)) (i : I)

/-- 同じ全変換の係数制限は、元の射影による Yoneda 図式から同じ分類頂点への変換。 -/
def weightedIndDensityCoefficientHomotopy :
    SSet.Homotopy ((SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫ indYoneda κ C)
      (SSet.const ((weightedIndClassification κ F hF).app
        (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i)))) := by
  let H := functorHomotopyPrecomp (weightedIndDensityHomotopy κ F hF)
    ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i))
  have hs : (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (weightedDensityProjection F) ≫ indYoneda κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫ indYoneda κ C := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, weightedDensityProjection_coefficient]
  have ht : (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveProjection (rightFibrationTotalDiagram F)) ≫
            weightedIndClassification κ F hF) =
      SSet.const ((weightedIndClassification κ F hF).app
        (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i))) := by
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, weightedNerveConstantLift_projection]
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

/-- 同じ係数変換の全円柱は、元の全変換の同じ係数での制限そのもの。 -/
lemma weightedIndDensityCoefficientHomotopy_h :
    (weightedIndDensityCoefficientHomotopy κ F hF i).h =
      ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷
          (Δ[1] : SSet.{u + 1})) ≫ (weightedIndDensityHomotopy κ F hF).h := rfl

/-- 包含後も元の同じ全円柱の制限を回収する。 -/
lemma weightedIndDensityCoefficientHomotopy_inclusion :
    (weightedIndDensityCoefficientHomotopy κ F hF i).h ≫ indInclusionPresheaf κ C =
      ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift (rightFibrationTotalDiagram F) i) ▷
          (Δ[1] : SSet.{u + 1})) ≫ (weightedDensityDiagramHomotopy F).h := by
  rw [weightedIndDensityCoefficientHomotopy_h, Category.assoc,
    weightedIndDensityHomotopy_inclusion]

/-- 同じ指定係数変換から得る、同じ頂点と全余錐を持つ実現データ。 -/
def weightedIndDensityCoefficientRealization :=
  F2.homotopyCoconeRealization (weightedIndDensityCoefficientHomotopy κ F hF i)

/-- 元の各段の全空間の密度図式上の、指定した全変換を実現する native な余錐。 -/
def weightedIndDensityCoefficientCocone :
    JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map (F.obj i).val.hom ≫ indYoneda κ C) :=
  (weightedIndDensityCoefficientRealization κ F hF i).cocone

lemma weightedIndDensityCoefficientCocone_vertex :
    (weightedIndDensityCoefficientCocone κ F hF i).vertex =
      (weightedIndClassification κ F hF).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex i)) :=
  (weightedIndDensityCoefficientRealization κ F hF i).vertex_eq

end SerrePositivity.InfinityCategories.F2.Ind
