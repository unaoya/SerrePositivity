module
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelHomModules
public import SerrePositivity.InfinityCategories.Derived.Gluing.KernelComparisonHomIso
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift

/-! native 代表加群と、同じ kernel 対象への制限 Hom 加群の実同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X : DGGluingObject R C D M)
local notation "G" => DGGluingObject R C D M
local notation "K" => dgGluingKernelComparisonFunctor R C D M
local notation "J" => dgGluingKernelHomModuleFunctor R C D M

/-- 全 Hom の比較同型を、同じ native 代表加群の全次数自然な同型へ組み立てる。 -/
def dgGluingKernelRepresentableModuleIso :
    ForgetEnrichment.of (Complex R) (representable R X) ≅
      ForgetEnrichment.of (Complex R) ((J).obj ((K).obj X)) :=
  moduleIsoMk R G (fun y => dgGluingKernelComparisonHomIso R C D M y.unop X)
    (by
      intro y z
      exact dgHomMap_contra_naturality K X y z)

lemma dgGluingKernelRepresentableModuleIso_hom_eval (Y : DGGluingObject R C D M) :
    (moduleEvaluation R G Y).map (dgGluingKernelRepresentableModuleIso R C D M X).hom =
      (dgGluingKernelComparisonHomIso R C D M Y X).hom :=
  moduleIsoMk_hom_eval R G _ _ Y

lemma dgGluingKernelRepresentableModuleIso_inv_eval (Y : DGGluingObject R C D M) :
    (moduleEvaluation R G Y).map (dgGluingKernelRepresentableModuleIso R C D M X).inv =
      (dgGluingKernelComparisonHomIso R C D M Y X).inv :=
  moduleIsoMk_inv_eval R G _ _ Y

end SerrePositivity.InfinityCategories
