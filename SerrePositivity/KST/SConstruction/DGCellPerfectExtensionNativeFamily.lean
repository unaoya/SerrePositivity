module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra

/-!
概要：固定 cell 上の Perf 延長の native 比較を一つの全関手族として構成する。
方針：同じ Perf 包含上で分解比較と実導来延長比較を貼り、前合成で各 graph を回収する。
規約：二つの graph に別々の比較を選ばない。元実延長を保持。
使われ方：中央射の同じ比較射を保つ全自然性の接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "C" => PerfectDGModule R (P)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)

/-- 概要：同じ Perf 包含上の実導来延長と元 dg 延長の一つの全比較。
方針：元 Perf 対象の射影性を使って三つの既存全比較を貼る。
規約：元の指定射と全 Hom を保持。使われ方：二 graph に共通する比較族。 -/
def dgCellPerfectExtensionNativeFamily (projection : DGFunctor R (P) E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection))) := by
  let H := dgModuleExtension R (P) E projection
  let hH : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R (P) M →
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (H.obj M) :=
    fun _ hM => dgModuleExtension_homotopicallyProjective R (P) E projection hM
  have a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (C) (P) (J)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
  have b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_underlyingIso R (P) E H hH).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (C) (P) (J))
  have c := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R (C) (P) (J)
    (fun M => M.property.1)).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  have b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (C) (P) (J) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (C) (P) (J) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion R (RightModule R (P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (P)))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity, H] using b
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using a ≪≫ b' ≪≫ c

private lemma nativeFamilyNaturality {X Y Z : SSet.{w}}
    [Quasicategory Y] [Quasicategory Z] {f g : X ⟶ Y} {p q : Y ⟶ Z}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g p a ≫ (e.precomp g).hom =
      (e.precomp f).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom]
  change (hoFunctor.map ((ihom X).map p)).toFunctor.map a ≫
      (hoFunctor.map ((pre g).app Z)).toFunctor.map e.hom =
    (hoFunctor.map ((pre f).app Z)).toFunctor.map e.hom ≫
      (hoFunctor.map ((ihom X).map q)).toFunctor.map a
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_whisker_exchange a e.hom

/-- 概要：共通 Perf 比較族は元の任意の全関手射に自然。
方針：同じ全比較と元射の二胞体交換則を適用する。
規約：元射の可逆性を仮定しない。使われ方：右軸から恒等への比較射の回収。 -/
lemma dgCellPerfectExtensionNativeFamily_naturality (projection : DGFunctor R (P) E)
    {X : SSet.{max (u + 1) v}} (f g : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (C)) (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) a ≫
      ((dgCellPerfectExtensionNativeFamily R B E projection).precomp g).hom =
    ((dgCellPerfectExtensionNativeFamily R B E projection).precomp f).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection))) a := by
  exact nativeFamilyNaturality a (dgCellPerfectExtensionNativeFamily R B E projection)

end SerrePositivity.KST.SConstruction
