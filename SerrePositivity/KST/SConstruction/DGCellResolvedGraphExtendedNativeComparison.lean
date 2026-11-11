module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeAugmentation
public import SerrePositivity.KST.SConstruction.DGCellPerfectExtensionNativeFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCellResolvedGraphProjective
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactor

/-!
概要：同じ射影的 graph の native 導来延長と実 dg 延長を全関手同型で比較する。
方針：同じ分解の生包含比較・D の射影性・元 graph 延長の包含比較を貼る。
規約：元実延長を保持。全 ν／lax 比較は別工程。
使われ方：resolved 商上の実 Perf 延長と native graph square の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
local notation "P" => DGCategoryCellResolution.Source R B
variable (F : DGFunctor R B B)
local notation "MF" => dgCellResolvedGraphModuleFunctor R B F
local notation "ρ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)

/-- 概要：同じ graph の実導来延長の生包含像は元 dg 延長と全比較される。
方針：同じ全分解比較を射影性の充足下で貼る。
規約：同じ graph 対象・同じ指定 dg 射を保持。
使われ方：native square を同じ実 Perf graph 延長へ移す。 -/
def dgCellResolvedGraphExtendedNativeComparison (projection : DGFunctor R (P) E) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((MF).comp (dgModuleExtension R (P) E projection))) := by
  let hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R (P) ((MF).obj x) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F
  let H := dgModuleExtension R (P) E projection
  let hH : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R (P) M →
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (H.obj M) :=
    fun _ hM => dgModuleExtension_homotopicallyProjective R (P) E projection hM
  have a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R (P) (P) (MF)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
  have b := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor_underlyingIso R (P) E H hH).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (P) (P) (MF))
  have c := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R (P) (P) (MF) hF).postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)
  have b' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (P) (P) (MF) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (P) (P) (MF) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgFullSubcategoryInclusion R (RightModule R (P)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R (P)))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity, H] using b
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc] using a ≪≫ b' ≪≫ c

/-- 概要：同じ graph の実 Perf 延長の包含像は元の実加群延長。
方針：元二つの厳密包含等号を合成する。規約：同じ指定射を保持。
使われ方：native 比較の終端を保存済み Perf 延長へ照合する。 -/
lemma dgCellResolvedGraphPerfectExtension_inclusion (projection : DGFunctor R (P) E) :
    (((dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)).comp
      (perfectDGExtension R (P) E projection)).comp (perfectDGModuleInclusion R E Set.univ)) =
      (MF).comp (dgModuleExtension R (P) E projection) := by
  rw [strictDGFunctor_comp_assoc, perfectDGExtension_inclusion,
    ← strictDGFunctor_comp_assoc, dgCellResolvedGraphPerfectFunctor_inclusion]


local notation "K" => dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ

/-- 概要：共通比較族の前合成始端は元 graph の同じ native 延長。
方針：元 graph の厳密包含等号を全 nerve へ写す。規約：同じ実対象を保持。
使われ方：前合成した比較の端点正規化。 -/
lemma dgCellResolvedGraphPerfectNativeFamily_source (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) ≫ (ρ)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) := by
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (K) (J)).symm.trans
      (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L) (dgCellResolvedGraphPerfectFunctor_inclusion R B F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)))
  simpa only [Category.assoc] using congrArg
    (fun L => (L ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) hI

/-- 概要：共通比較族の前合成終端は保存済み実 Perf 延長の包含像。
方針：元二つの包含等号を全 nerve の合成で照合する。
規約：元の同じ実延長を保持。使われ方：前合成した比較の端点正規化。 -/
lemma dgCellResolvedGraphPerfectNativeFamily_target (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((((K).comp (perfectDGExtension R (P) E projection))).comp
        (perfectDGModuleInclusion R E Set.univ)) := by
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (J) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (K) (J)).symm.trans
      (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L) (dgCellResolvedGraphPerfectFunctor_inclusion R B F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)))
  rw [dgCellResolvedGraphPerfectExtension_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    ← Category.assoc, hI]

/-- 概要：native graph の実導来延長を同じ実 Perf 延長の包含像へ全比較する。
方針：共通 Perf 比較族の前合成を元二端点へ正規化する。
規約：D の射影性を充足済み。使われ方：元比較射に自然な同じ Perf 成分の回収。 -/
def dgCellResolvedGraphPerfectExtendedNativeComparison (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (MF) ≫ (ρ)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R (P) E projection ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (((K).comp (perfectDGExtension R (P) E projection)).comp
          (perfectDGModuleInclusion R E Set.univ))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgCellPerfectExtensionNativeFamily R B E projection).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K)))
    (dgCellResolvedGraphPerfectNativeFamily_source R B E F projection)
    (dgCellResolvedGraphPerfectNativeFamily_target R B E F projection)

/-- 概要：指定した graph 比較は共通比較族の同じ前合成そのもの。
方針：端点正規化の型付き回収を使う。規約：比較の値を選び直さない。
使われ方：元の任意の比較射に対する全自然性の輸送。 -/
lemma dgCellResolvedGraphPerfectExtendedNativeComparison_family_heq
    (projection : DGFunctor R (P) E) :
    HEq (dgCellResolvedGraphPerfectExtendedNativeComparison R B E F projection)
      ((dgCellPerfectExtensionNativeFamily R B E projection).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (K))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _

end SerrePositivity.KST.SConstruction
