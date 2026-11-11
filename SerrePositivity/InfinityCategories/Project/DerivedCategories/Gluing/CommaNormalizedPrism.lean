module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CommaNormalizedCochainLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CochainAugmentationModelInput

/-! 標準閉射の実前後合成で引き戻した恒等 comma prism は、負 primitive の全明示族に一致する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded CochainComplex HomComplex MonoidalCategory
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : DGFunctor R C E) (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)

lemma dgGluingCommaNormalizedPrism_model :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom R C E F X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPinchedPrism R E X.replacement (F.obj Y.source) =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso X Y (A := R)).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism R E X.replacement (F.obj Y.source) _
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedReplacement R C E F X Y)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedSource R C E F X Y)
          (-_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedNegativePrimitive_boundary R C E F X Y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCochainAugmentationPrism_model_input,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaNormalizedHom_eq_cochainLift]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
