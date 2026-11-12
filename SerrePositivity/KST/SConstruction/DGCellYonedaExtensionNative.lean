module
public import SerrePositivity.KST.SConstruction.DGCellPerfectExtensionNativeFamily
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionYonedaNerveIso
/-!
概要：元 cell Yoneda の native 商延長を同じ商射影の Yoneda へ全比較する。
方針：既存の全 Perf 比較族を元 Yoneda へ前合成し元代表延長比較を合成する。
規約：元指定射・全 Hom・同じ実 Yoneda を保持する。
使われ方：実逆回転から固定 ν の同じ resolved 射影への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "Y" => dgYoneda R (P)
local notation "YP" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R (P)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)

/-- 概要：元 Yoneda の native 延長の全包含像は同じ元実 dg 延長。
方針：既存の同じ全 Perf 比較族を元 perfect Yoneda へ前合成する。
規約：新しい分解・比較を選ばない。使われ方：同じ商射影の元 Yoneda 回収の第一因子。 -/
def dgCellYonedaExtensionNativeComparison (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) ≫ (ρ)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((Y).comp (dgModuleExtension R (P) E projection))) := by
  let e := (dgCellPerfectExtensionNativeFamily R B E projection).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (YP))
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (YP) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (YP) (J)).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion R (P)))
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (YP) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) ≫ (ρ)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) ≫ (ρ)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) := by
    simpa only [Category.assoc] using congrArg
      (fun f => ((f ≫ (ρ)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) hj
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (YP) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((Y).comp (dgModuleExtension R (P) E projection)) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, ← strictDGFunctor_comp_assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hs ht

/-- 概要：元 Yoneda の native 延長は同じ指定射の元 Yoneda と全比較される。
方針：同じ全 Perf 前合成比較と D 正本の全代表延長比較を合成する。
規約：元の全自然変換を保持。使われ方：同じ resolved 射影の全回収。 -/
def dgCellYonedaProjectionNativeComparison (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Y) ≫ (ρ)) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (projection.comp (dgYoneda R E))) :=
  (dgCellYonedaExtensionNativeComparison R B E projection).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionYonedaStrict R (P) E projection)
      (fun x => (dgModuleExtensionRepresentableIso R (P) E projection x).hom)
      (fun _ => rfl)
      (fun x => (dgModuleExtensionRepresentableIso R (P) E projection x).isIso_hom))
end SerrePositivity.KST.SConstruction
