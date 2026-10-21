module
public import SerrePositivity.InfinityCategories.Derived.DGKernelClassicalComparison
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeClassicalComparison
/-!
概要：元の一般 kernel の主導来同値を、実出力分解の半自由出力射影の H⁰ 同値へ移す。
方針：同じ augmentation の自然同型と半自由模型の主導来比較同値を使う。
規約：∞ 圏同値には全高次 Hom の検査がなお必要。使われ方：一般 Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 元の主導来 kernel が同値なら、同じ実半自由出力射影の H⁰ も同値。 -/
lemma dgKernelResolutionReplacement_onHomotopy_isEquivalence
    (P : Bimodule R E D) [(Morita.kernelDerivedTensorOnBimodule R D E P).IsEquivalence] :
    (dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E
      (dgSemifreeKernelModuleDG R D E P)).onHomotopy.IsEquivalence := by
  let F := dgSemifreeKernelModuleDG R D E P
  let S := dgModuleResolutionSourceHomotopyEquivalence R (SemifreeDGModules R D) E F
  let G := dgModuleFunctorResolutionReplacement R (SemifreeDGModules R D) E F
  have e : dgModuleOutputResolutionClassical R (SemifreeDGModules R D) E F ≅
      dgSemifreeModuleToDerived R D ⋙ Morita.kernelDerivedTensorOnBimodule R D E P :=
    dgKernelOutputResolutionClassicalComparisonIso R D E P
  have : (dgModuleOutputResolutionClassical R (SemifreeDGModules R D) E F).IsEquivalence :=
    Functor.isEquivalence_of_iso e.symm
  have h : (S.inverse ⋙ G.onHomotopy ⋙ dgSemifreeModuleToDerived R E).IsEquivalence := this
  have : (G.onHomotopy ⋙ dgSemifreeModuleToDerived R E).IsEquivalence :=
    Functor.isEquivalence_of_comp_left S.inverse _
  exact Functor.isEquivalence_of_comp_right G.onHomotopy (dgSemifreeModuleToDerived R E)
end SerrePositivity.InfinityCategories
