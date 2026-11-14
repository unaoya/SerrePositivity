module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.Kernels.KernelHomModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomPostHomotopy

/-! 制限 Hom 加群関手の同じ実閉射の評価は、kernel comma 内の実後合成。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
    (Morita.kernelTensor R D C M))
  (f : ForgetEnrichment.of (Complex R) Y ⟶ ForgetEnrichment.of (Complex R) Z)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R (RightModule R D) (RightModule R C)
  (Morita.kernelTensor R D C M)
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelComparisonFunctor R C D M
local notation "J" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor R C D M

/-- 閉射の全 Hom 作用を単位から評価すると、同じ kernel 閉後合成を回収。 -/
lemma dgGluingKernelHomModuleFunctor_closed_eval :
    (moduleEvaluation R G X).map ((J).onClosed.map f) =
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((K).obj X)) f := by
  rw [moduleEvaluation_map]
  change mapFromUnit R (homObject R E ((K).obj X) Y) (homObject R E ((K).obj X) Z)
    ((ForgetEnrichment.homTo (Complex R) f ≫ (J).map Y Z) ≫ moduleHomπ R G _ _ X) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingKernelHomModuleFunctor_map_π]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftRepresentable_closed R E ((K).obj X) f

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
