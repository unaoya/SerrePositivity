module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveResolutionIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorHomologyDetection
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ標準射影分解を使う、既存の主導来加群圏間の作用。 -/
def dgModuleClassicalDerivedFunctor (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.DifferentialGraded.DerivedModuleCategory R D ⥤ DerivedModuleCategory R E :=
  _root_.SerrePositivity.DifferentialGraded.moduleDerivedResolutionFunctor R D (_root_.SerrePositivity.DifferentialGraded.moduleCanonicalProjectiveResolution R D) ⋙
    F.onHomotopy ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E
/-- 主導来作用と射影的模型上の同じ H⁰ 関手は一つの自然同型で比較される。 -/
def dgProjectiveModuleDerivedFunctorIso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R D ⋙ dgModuleClassicalDerivedFunctor R D E F ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E := by
  let I := dgFullSubcategoryInclusion R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  let J := dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E)
  let G := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF
  have hd : G.comp J = I.comp F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction_inclusion R
    (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E) F _ _ hF
  have he : G.onHomotopy ⋙ J.onHomotopy = I.onHomotopy ⋙ F.onHomotopy := by
    simpa only [_root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_comp] using congrArg (fun H => H.onHomotopy) hd
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveDerivedResolutionIso R D)
      (F.onHomotopy ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso he.symm) (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E) ≪≫
    Functor.associator _ _ _
/-- 主導来作用が Morita 同値なら、同じ dg 関手の半自由模型上の実 ∞ 作用も同値。 -/
theorem dgModuleDerivedFunctor_isQCatEquivalence_of_classical
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
    [(dgModuleClassicalDerivedFunctor R D E F).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D E F hF) := by
  have : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy ⋙
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E).IsEquivalence :=
    Functor.isEquivalence_of_iso (dgProjectiveModuleDerivedFunctorIso R D E F hF)
  have : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).onHomotopy.IsEquivalence :=
    Functor.isEquivalence_of_comp_right _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleToDerived R E)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_isQCatEquivalence_of_ho R D E F hF
/-- 主導来延長が同値となる dg 関手について、実相対 tensor ∞ 関手も同値。 -/
theorem dgModuleExtensionInfinity_isQCatEquivalence_of_morita (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
    [(_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R D E F) := by
  have : (dgModuleClassicalDerivedFunctor R D E (_root_.SerrePositivity.DifferentialGraded.dgModuleExtension R D E F)).IsEquivalence := by
    change (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence
    infer_instance
  exact dgModuleDerivedFunctor_isQCatEquivalence_of_classical R D E _ _
/-- 任意の dg 準同値は、半自由加群の導来 ∞ 圏の実相対 tensor 同値を与える。 -/
theorem dgModuleExtensionInfinity_isQCatEquivalence_of_quasiEquivalence
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (hF : _root_.SerrePositivity.DifferentialGraded.QuasiEquivalence F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R D E F) := by
  have : (_root_.SerrePositivity.DifferentialGraded.dgDerivedExtension R D E F).IsEquivalence :=
    (_root_.SerrePositivity.DifferentialGraded.dgFunctorDerivedEquivalence R D E F hF).isEquivalence_functor
  exact dgModuleExtensionInfinity_isQCatEquivalence_of_morita R D E F
end SerrePositivity.InfinityCategories.Project.DerivedCategories
