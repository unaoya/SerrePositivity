module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphNativeAugmentation
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

/-- 概要：native graph の実導来延長を同じ実 Perf 延長の包含像へ全比較する。
方針：実加群比較の終端に元全 Hom 包含等号を代入する。
規約：D の射影性を充足済み。使われ方：同じ resolved 商上の Perf 成分の回収。 -/
def dgCellResolvedGraphPerfectExtendedNativeComparison (projection : DGFunctor R (P) E) :
    FunctorIso
      ((dgNerve.map (MF) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
      (dgNerve.map (((dgCellResolvedGraphPerfectFunctor R B F
        (dgCellResolvedGraph_projective R B F)).comp (perfectDGExtension R (P) E projection)).comp
          (perfectDGModuleInclusion R E Set.univ))) := by
  rw [dgCellResolvedGraphPerfectExtension_inclusion]
  exact dgCellResolvedGraphExtendedNativeComparison R B E F projection

end SerrePositivity.KST.SConstruction
