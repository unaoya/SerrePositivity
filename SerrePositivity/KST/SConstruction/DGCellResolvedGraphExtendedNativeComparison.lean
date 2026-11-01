module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeAugmentation
public import SerrePositivity.KST.SConstruction.DGCellPerfectExtensionNativeFamily
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence
public import SerrePositivity.InfinityCategories.Derived.DGCellResolvedGraphProjective
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor

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
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)

/-- 概要：同じ graph の実導来延長の生包含像は元 dg 延長と全比較される。
方針：同じ全分解比較を射影性の充足下で貼る。
規約：同じ graph 対象・同じ指定 dg 射を保持。
使われ方：native square を同じ実 Perf graph 延長へ移す。 -/
def dgCellResolvedGraphExtendedNativeComparison (projection : DGFunctor R (P) E) : FunctorIso
    ((dgNerve.map (MF) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
    (dgNerve.map ((MF).comp (dgModuleExtension R (P) E projection))) := by
  let hF : ∀ x, dgModuleProjectiveProperty R (P) ((MF).obj x) :=
    dgCellResolvedGraph_projective R B F
  let H := dgModuleExtension R (P) E projection
  let hH : ∀ M, dgModuleProjectiveProperty R (P) M →
      dgModuleProjectiveProperty R E (H.obj M) :=
    fun _ hM => dgModuleExtension_homotopicallyProjective R (P) E projection hM
  have a := FunctorIso.postcomp
    (dgModuleResolvedInfinity_rawFactorIso R (P) (P) (MF)).symm
    (dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
  have b := (dgModuleDerivedFunctor_underlyingIso R (P) E H hH).precomp
    (dgModuleResolvedInfinity R (P) (P) (MF))
  have c := (dgModuleResolvedInfinity_inclusionIso R (P) (P) (MF) hF).postcomp
    (dgNerve.map H)
  have b' : FunctorIso
      (dgModuleResolvedInfinity R (P) (P) (MF) ≫
        dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
      ((dgModuleResolvedInfinity R (P) (P) (MF) ≫ dgNerve.map
        (dgFullSubcategoryInclusion R (RightModule R (P)) (dgModuleSemifreeProperty R (P)))) ≫
          dgNerve.map H) := by
    simpa only [dgNerve.map_comp, Category.assoc, dgModuleExtensionInfinity, H] using b
  simpa only [dgNerve.map_comp, Category.assoc] using a ≪≫ b' ≪≫ c

/-- 概要：同じ graph の実 Perf 延長の包含像は元の実加群延長。
方針：元二つの厳密包含等号を合成する。規約：同じ指定射を保持。
使われ方：native 比較の終端を保存済み Perf 延長へ照合する。 -/
lemma dgCellResolvedGraphPerfectExtension_inclusion (projection : DGFunctor R (P) E) :
    (((dgCellResolvedGraphPerfectFunctor R B F (dgCellResolvedGraph_projective R B F)).comp
      (perfectDGExtension R (P) E projection)).comp (perfectDGModuleInclusion R E Set.univ)) =
      (MF).comp (dgModuleExtension R (P) E projection) := by
  rw [strictDGFunctor_comp_assoc, perfectDGExtension_inclusion,
    ← strictDGFunctor_comp_assoc, dgCellResolvedGraphPerfectFunctor_inclusion]


local notation "K" => dgCellResolvedGraphPerfectFunctor R B F (dgCellResolvedGraph_projective R B F)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ

/-- 概要：共通比較族の前合成始端は元 graph の同じ native 延長。
方針：元 graph の厳密包含等号を全 nerve へ写す。規約：同じ実対象を保持。
使われ方：前合成した比較の端点正規化。 -/
lemma dgCellResolvedGraphPerfectNativeFamily_source (projection : DGFunctor R (P) E) :
    dgNerve.map (K) ≫ ((dgNerve.map (J) ≫ (ρ)) ≫
      dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I)) =
    ((dgNerve.map (MF) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I)) := by
  have hI : dgNerve.map (K) ≫ dgNerve.map (J) = dgNerve.map (MF) :=
    (dgNerve.map_comp (K) (J)).symm.trans
      (congrArg (fun L => dgNerve.map L) (dgCellResolvedGraphPerfectFunctor_inclusion R B F
        (dgCellResolvedGraph_projective R B F)))
  simpa only [Category.assoc] using congrArg
    (fun L => (L ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I)) hI

/-- 概要：共通比較族の前合成終端は保存済み実 Perf 延長の包含像。
方針：元二つの包含等号を全 nerve の合成で照合する。
規約：元の同じ実延長を保持。使われ方：前合成した比較の端点正規化。 -/
lemma dgCellResolvedGraphPerfectNativeFamily_target (projection : DGFunctor R (P) E) :
    dgNerve.map (K) ≫ dgNerve.map ((J).comp (dgModuleExtension R (P) E projection)) =
      dgNerve.map ((((K).comp (perfectDGExtension R (P) E projection))).comp
        (perfectDGModuleInclusion R E Set.univ)) := by
  have hI : dgNerve.map (K) ≫ dgNerve.map (J) = dgNerve.map (MF) :=
    (dgNerve.map_comp (K) (J)).symm.trans
      (congrArg (fun L => dgNerve.map L) (dgCellResolvedGraphPerfectFunctor_inclusion R B F
        (dgCellResolvedGraph_projective R B F)))
  rw [dgCellResolvedGraphPerfectExtension_inclusion, dgNerve.map_comp, dgNerve.map_comp,
    ← Category.assoc, hI]

/-- 概要：native graph の実導来延長を同じ実 Perf 延長の包含像へ全比較する。
方針：共通 Perf 比較族の前合成を元二端点へ正規化する。
規約：D の射影性を充足済み。使われ方：元比較射に自然な同じ Perf 成分の回収。 -/
def dgCellResolvedGraphPerfectExtendedNativeComparison (projection : DGFunctor R (P) E) :
    FunctorIso
      ((dgNerve.map (MF) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
      (dgNerve.map (((K).comp (perfectDGExtension R (P) E projection)).comp
          (perfectDGModuleInclusion R E Set.univ))) :=
  F2.functorIsoOfEq
    ((dgCellPerfectExtensionNativeFamily R B E projection).precomp (dgNerve.map (K)))
    (dgCellResolvedGraphPerfectNativeFamily_source R B E F projection)
    (dgCellResolvedGraphPerfectNativeFamily_target R B E F projection)

/-- 概要：指定した graph 比較は共通比較族の同じ前合成そのもの。
方針：端点正規化の型付き回収を使う。規約：比較の値を選び直さない。
使われ方：元の任意の比較射に対する全自然性の輸送。 -/
lemma dgCellResolvedGraphPerfectExtendedNativeComparison_family_heq
    (projection : DGFunctor R (P) E) :
    HEq (dgCellResolvedGraphPerfectExtendedNativeComparison R B E F projection)
      ((dgCellPerfectExtensionNativeFamily R B E projection).precomp (dgNerve.map (K))) :=
  F2.functorIsoOfEq_heq _ _ _

end SerrePositivity.KST.SConstruction
