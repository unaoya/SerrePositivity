module
public import SerrePositivity.InfinityCategories.Derived.DGModuleRawOutputPrecompHom
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedChangeRawValue
public import SerrePositivity.InfinityCategories.Derived.FunctorHomConjugationPrecomp
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedHomFunctor
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：実後続双加群射の raw・導来射作用を、同じ端点輸送済み前合成作用へ同定する。
方針：元の raw factor の同じ順方向・逆方向を保ち、共役式を型付きで照合する。
規約：射の可逆性・kernel の平坦性を要求しない。使われ方：元の κ の右変数自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (E K : Type v)
  [DGCategory R E] [Small.{u} E] [DGCategory R K] [Small.{u} K]
lemma dgKernelDerivedRawFactorIso_hom_module_heq (Q : BimoduleCategory R K E) :
    HEq (dgKernelDerivedRawFactorIso R E K Q).hom
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q))).hom := by
  have ht : (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) ≫ dgNerve.map
          (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q))) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) =
    dgNerve.map (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q)) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) := by
    simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp]
  exact functorIso_hom_heq_of_endpoint_heq _ _ rfl ht
    (dgKernelDerivedRawFactorIso_module_heq R E K Q)
lemma dgKernelDerivedRawFactorIso_inv_module_heq (Q : BimoduleCategory R K E) :
    HEq (dgKernelDerivedRawFactorIso R E K Q).inv
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q))).inv := by
  have ht : (dgNerve.map (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)) ≫ dgNerve.map
          (Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q))) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) =
    dgNerve.map (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q)) ≫
      dgModuleResolvedInfinity R (RightModule R K) K (DGFunctor.id (RightModule R K)) := by
    simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp]
  exact functorIso_inv_heq_of_endpoint_heq _ _ rfl ht
    (dgKernelDerivedRawFactorIso_module_heq R E K Q)
variable {Q0 Q1 : BimoduleCategory R K E} (g : Q0 ⟶ Q1)
local notation "H0" => Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q0)
local notation "H1" => Morita.kernelTensor R E K (BimoduleCategory.underlying R K E Q1)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)
local notation "L" => dgModuleResolvedInfinity R (RightModule R K) K
  (DGFunctor.id (RightModule R K))
lemma dgKernelResolvedRawFunctorHomFunctor_map_precomp_heq :
    HEq (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1
      (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
        ((dgKernelTensorFunctorHomFunctor R E K).map g)))
      ((dgKernelResolvedRawFunctorHomFunctor R E K).map g) := by
  have h0 := dgModuleRawOutputPrecompHom_heq R E K (SemifreeDGModules R E) I H0 H1
    (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
      ((dgKernelTensorFunctorHomFunctor R E K).map g))
  have h1 := functorHomPrecomp_postcomp (dgNerve.map H0) (dgNerve.map H1)
    (dgNerve.map I) L ((dgKernelTensorFunctorHomFunctor R E K).map g)
  exact h0.trans (heq_of_eq h1.symm)
lemma dgKernelDerivedFunctorHomFunctor_map_rawPrecomp :
    (dgKernelDerivedFunctorHomFunctor R E K).map g =
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q0))).hom ≫
      dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1
        (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
          ((dgKernelTensorFunctorHomFunctor R E K).map g)) ≫
      (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
        (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q1))).inv := by
  have ht (Q : BimoduleCategory R K E) :
      (dgNerve.map I ≫ dgNerve.map (Morita.kernelTensor R E K
        (BimoduleCategory.underlying R K E Q))) ≫ L =
      dgNerve.map (dgSemifreeKernelModuleDG R E K
        (BimoduleCategory.underlying R K E Q)) ≫ L := by
    simp only [dgSemifreeKernelModuleDG, dgNerve.map_comp]
  have h0 := functorHom_comp_heq
    (f := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q0))
    (g := (dgNerve.map I ≫ dgNerve.map H0) ≫ L)
    (h := (dgNerve.map I ≫ dgNerve.map H1) ≫ L)
    (f' := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q0))
    (g' := dgNerve.map (dgSemifreeKernelModuleDG R E K
      (BimoduleCategory.underlying R K E Q0)) ≫ L)
    (h' := dgNerve.map (dgSemifreeKernelModuleDG R E K
      (BimoduleCategory.underlying R K E Q1)) ≫ L)
    (dgKernelDerivedRawFactorIso R E K Q0).hom
    ((dgKernelResolvedRawFunctorHomFunctor R E K).map g)
    (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
      (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q0))).hom
    (dgModuleRawOutputPrecompHom R E K (SemifreeDGModules R E) I H0 H1
      (functorHomPostcomp (dgNerve.map H0) (dgNerve.map H1) L
        ((dgKernelTensorFunctorHomFunctor R E K).map g)))
    rfl (ht Q0) (ht Q1) (dgKernelDerivedRawFactorIso_hom_module_heq R E K Q0)
    (dgKernelResolvedRawFunctorHomFunctor_map_precomp_heq R E K g).symm
  have h1 := functorHom_comp_heq
    (f := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q0))
    (g := (dgNerve.map I ≫ dgNerve.map H1) ≫ L)
    (h := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q1))
    (f' := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q0))
    (g' := dgNerve.map (dgSemifreeKernelModuleDG R E K
      (BimoduleCategory.underlying R K E Q1)) ≫ L)
    (h' := dgKernelDerivedInfinity R E K (BimoduleCategory.underlying R K E Q1))
    _ (dgKernelDerivedRawFactorIso R E K Q1).inv
    _ (dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R E) K
      (dgSemifreeKernelModuleDG R E K (BimoduleCategory.underlying R K E Q1))).inv
    rfl (ht Q1) rfl h0 (dgKernelDerivedRawFactorIso_inv_module_heq R E K Q1)
  simpa only [dgKernelDerivedFunctorHomFunctor, Category.assoc] using! eq_of_heq h1
end SerrePositivity.InfinityCategories
