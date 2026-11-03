module
public import SerrePositivity.InfinityCategories.Derived.DGProjectiveResolutionIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorHomologyDetection
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
/-!
概要：既存の主導来加群圏上の Morita 同値を、半自由模型の実 ∞ 圏同値へ昇格する。
方針：標準分解の同じ自然同型で射影的 H⁰ 関手を比較し、全 source shift の Hom を検査する。
規約：H⁰ の同値だけで高次 Hom を省略しない。使われ方：β5 の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ標準射影分解を使う、既存の主導来加群圏間の作用。 -/
def dgModuleClassicalDerivedFunctor (F : DGFunctor R (RightModule R D) (RightModule R E)) :
    DerivedModuleCategory R D ⥤ DerivedModuleCategory R E :=
  moduleDerivedResolutionFunctor R D (moduleCanonicalProjectiveResolution R D) ⋙
    F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E
/-- 主導来作用と射影的模型上の同じ H⁰ 関手は一つの自然同型で比較される。 -/
def dgProjectiveModuleDerivedFunctorIso
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M)) :
    dgProjectiveModuleToDerived R D ⋙ dgModuleClassicalDerivedFunctor R D E F ≅
      (dgProjectiveModuleFunctor R D E F hF).onHomotopy ⋙ dgProjectiveModuleToDerived R E := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)
  let J := dgFullSubcategoryInclusion R (RightModule R E) (dgModuleProjectiveProperty R E)
  let G := dgProjectiveModuleFunctor R D E F hF
  have hd : G.comp J = I.comp F := dgFullFunctorRestriction_inclusion R
    (RightModule R D) (RightModule R E) F _ _ hF
  have he : G.onHomotopy ⋙ J.onHomotopy = I.onHomotopy ⋙ F.onHomotopy := by
    simpa only [DGFunctor.onHomotopy_comp] using congrArg (fun H => H.onHomotopy) hd
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (dgProjectiveDerivedResolutionIso R D)
      (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso he.symm) (moduleHomotopyToDerivedClosed R E) ≪≫
    Functor.associator _ _ _
/-- 主導来作用が Morita 同値なら、同じ dg 関手の半自由模型上の実 ∞ 作用も同値。 -/
theorem dgModuleDerivedFunctor_isQCatEquivalence_of_classical
    (F : DGFunctor R (RightModule R D) (RightModule R E))
    (hF : ∀ M, dgModuleProjectiveProperty R D M → dgModuleProjectiveProperty R E (F.obj M))
    [(dgModuleClassicalDerivedFunctor R D E F).IsEquivalence] :
    IsQCatEquivalence (dgModuleDerivedFunctor R D E F hF) := by
  have : ((dgProjectiveModuleFunctor R D E F hF).onHomotopy ⋙
      dgProjectiveModuleToDerived R E).IsEquivalence :=
    Functor.isEquivalence_of_iso (dgProjectiveModuleDerivedFunctorIso R D E F hF)
  have : (dgProjectiveModuleFunctor R D E F hF).onHomotopy.IsEquivalence :=
    Functor.isEquivalence_of_comp_right _ (dgProjectiveModuleToDerived R E)
  exact dgModuleDerivedFunctor_isQCatEquivalence_of_ho R D E F hF
/-- 主導来延長が同値となる dg 関手について、実相対 tensor ∞ 関手も同値。 -/
theorem dgModuleExtensionInfinity_isQCatEquivalence_of_morita (F : DGFunctor R D E)
    [(dgDerivedExtension R D E F).IsEquivalence] :
    IsQCatEquivalence (dgModuleExtensionInfinity R D E F) := by
  have : (dgModuleClassicalDerivedFunctor R D E (dgModuleExtension R D E F)).IsEquivalence := by
    change (dgDerivedExtension R D E F).IsEquivalence
    infer_instance
  exact dgModuleDerivedFunctor_isQCatEquivalence_of_classical R D E _ _
/-- 任意の dg 準同値は、半自由加群の導来 ∞ 圏の実相対 tensor 同値を与える。 -/
theorem dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence
    (F : DGFunctor R D E) (hF : QuasiEquivalence F) :
    IsQCatEquivalence (dgModuleExtensionInfinity R D E F) := by
  have : (dgDerivedExtension R D E F).IsEquivalence :=
    (dgFunctorDerivedEquivalence R D E F hF).isEquivalence_functor
  exact dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F
end SerrePositivity.InfinityCategories
