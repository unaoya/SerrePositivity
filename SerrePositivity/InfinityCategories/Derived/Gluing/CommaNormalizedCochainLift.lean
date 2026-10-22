module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaNormalizedHomLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.CochainIdentityCommaLift

/-! 実前後合成の正規化は、元の負 primitive から作る明示 cochain lift そのもの。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y : DGFunctorCommaObject R C E F)

lemma dgGluingCommaNormalizedNegativePrimitive_boundary :
    δ (-1) 0 (-dgFunctorCommaPrimitive R C E F X Y) =
      Cochain.ofHom (dgGluingCommaNormalizedSource R C E F X Y -
        dgGluingCommaNormalizedReplacement R C E F X Y) := by
  rw [δ_neg]
  exact neg_eq_iff_add_eq_zero.mpr (dgGluingCommaNormalizedPrimitive_boundary R C E F X Y)

lemma dgGluingCommaNormalizedHom_eq_cochainLift :
    dgGluingCommaNormalizedHom R C E F X Y =
      dgGluingCochainIdentityCommaLift R E X.replacement (F.obj Y.source) _
        (dgGluingCommaNormalizedReplacement R C E F X Y)
        (dgGluingCommaNormalizedSource R C E F X Y)
        (-dgFunctorCommaPrimitive R C E F X Y)
        (dgGluingCommaNormalizedNegativePrimitive_boundary R C E F X Y) := by
  rw [dgGluingCommaNormalizedHom_eq_lift, dgGluingCochainIdentityCommaLift]
  simp only [neg_neg, dgGluingCommaNormalizedHomLift]

end SerrePositivity.InfinityCategories
