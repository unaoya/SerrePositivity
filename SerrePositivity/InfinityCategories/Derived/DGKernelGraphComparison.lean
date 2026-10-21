module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedDerivedComparison
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
/-!
概要：任意双加群作用の実 graph を、既存の相対 tensor ∞ 関手に比較する。
方針：元の graph dg 関手の厳密等式と二つの実導来化の全関手比較を使う。
規約：同じ元の graph を保持する。使われ方：一般作用の graph 整合性と完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 一般双加群作用の同じ graph は、既存の実相対 tensor ∞ 関手と同型。 -/
def dgKernelDerivedInfinity_graphIso (F : DGFunctor R D E) :
    FunctorIso (dgKernelDerivedInfinity R D E (functorGraph R D E F))
      (dgModuleExtensionInfinity R D E F) := by
  have e := dgModuleResolvedInfinity_derivedFunctorIso R D E (dgModuleExtension R D E F)
    (fun _ h => dgModuleExtension_homotopicallyProjective R D E F h)
  change FunctorIso (dgModuleResolvedInfinity R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E (functorGraph R D E F))) _
  rw [dgSemifreeKernelModuleDG, Morita.kernelTensor_graph]
  exact e
/-- 同じ一般作用の graph 制限は完全関手。 -/
lemma dgKernelDerivedInfinity_graph_isExactFunctor (F : DGFunctor R D E) :
    IsExactFunctor (dgKernelDerivedInfinity R D E (functorGraph R D E F)) := by
  let := dgModuleExtensionInfinity_isExactFunctor R D E F
  exact isExactFunctor_of_functorIso (dgKernelDerivedInfinity_graphIso R D E F).symm
end SerrePositivity.InfinityCategories
