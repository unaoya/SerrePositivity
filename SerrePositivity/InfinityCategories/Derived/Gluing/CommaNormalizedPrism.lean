module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainAugmentationModelInput

/-! 標準閉射の実前後合成で引き戻した恒等 comma prism は、負 primitive の全明示族に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [DGCategory R C] [DGCategory R E]
  (F : DGFunctor R C E) (X Y : DGFunctorCommaObject R C E F)

lemma dgGluingCommaNormalizedPrism_model :
    (Δ[1] ◁ pinchedHomChainMap (D := DGFunctorCommaObject R C E F)
      (dgGluingCommaNormalizedHom R C E F X Y)) ≫
        dgGluingIdentityCommaPinchedPrism R E X.replacement (F.obj Y.source) =
      (Δ[1] ◁ (pinchedComplexModelIso X Y (A := R)).hom) ≫
        dgGluingCochainAugmentationPrism R E X.replacement (F.obj Y.source) _
          (dgGluingCommaNormalizedReplacement R C E F X Y)
          (dgGluingCommaNormalizedSource R C E F X Y)
          (-dgFunctorCommaPrimitive R C E F X Y)
          (dgGluingCommaNormalizedNegativePrimitive_boundary R C E F X Y) := by
  rw [dgGluingCochainAugmentationPrism_model_input,
    dgGluingCommaNormalizedHom_eq_cochainLift]
  rfl

end SerrePositivity.InfinityCategories
