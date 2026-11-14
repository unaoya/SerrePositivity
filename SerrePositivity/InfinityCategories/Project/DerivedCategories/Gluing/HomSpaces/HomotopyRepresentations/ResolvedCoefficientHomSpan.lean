module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.ResolvedModuleValues
public import SerrePositivity.DifferentialGraded.Derived.Projective

public import SerrePositivity.DifferentialGraded.Module.Basic

/-! 実分解 Hom と元の係数を、同じ二つの augmentation からの準同型 span で比較する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (c : C) (N : RightModule R C)

abbrev dgGluingResolvedCoefficientHomComplex : Complex R :=
  moduleHom R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C (representable R c)).val
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C N).val

abbrev dgGluingResolvedCoefficientMiddleComplex : Complex R :=
  moduleHom R C (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C (representable R c)).val N

def dgGluingResolvedCoefficientHomPost :
    dgGluingResolvedCoefficientHomComplex R C c N ⟶
      dgGluingResolvedCoefficientMiddleComplex R C c N :=
  eHomWhiskerLeft (Complex R)
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule R C (representable R c)).val)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C N)

def dgGluingResolvedCoefficientYonedaPre :
    N.obj (Opposite.op c) ⟶ dgGluingResolvedCoefficientMiddleComplex R C c N :=
  (dgYonedaIso R c N).inv ≫
    eHomWhiskerRight (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C (representable R c))
      (ForgetEnrichment.of (Complex R) N)

lemma dgGluingResolvedCoefficientHomPost_quasiIso :
    QuasiIso (dgGluingResolvedCoefficientHomPost R C c N) :=
  moduleHomotopicallyProjective_postcompose_quasiIso R C
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule_projective R C (representable R c))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C N)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation_quasiIso R C N)

lemma dgGluingResolvedCoefficientYonedaPre_quasiIso :
    QuasiIso (dgGluingResolvedCoefficientYonedaPre R C c N) := by
  let : QuasiIso (eHomWhiskerRight (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C (representable R c))
      (ForgetEnrichment.of (Complex R) N)) :=
    moduleHomotopicallyProjective_precompose_quasiIso R C
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModule_projective R C (representable R c))
      (representable_homotopicallyProjective R C c)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation R C (representable R c))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingResolvedModuleAugmentation_quasiIso R C (representable R c))
      (ForgetEnrichment.of (Complex R) N)
  dsimp only [dgGluingResolvedCoefficientYonedaPre]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
