module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedUnderlyingIso
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra

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
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)

/-- 概要：同じ Perf 包含上の実導来延長と元 dg 延長の一つの全比較。
方針：元 Perf 対象の射影性を使って三つの既存全比較を貼る。
規約：元の指定射と全 Hom を保持。使われ方：二 graph に共通する比較族。 -/
def dgCellPerfectExtensionNativeFamily (projection : DGFunctor R (P) E) : FunctorIso
    ((dgNerve.map (J) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
    (dgNerve.map ((J).comp (dgModuleExtension R (P) E projection))) := by
  let H := dgModuleExtension R (P) E projection
  let hH : ∀ M, dgModuleProjectiveProperty R (P) M →
      dgModuleProjectiveProperty R E (H.obj M) :=
    fun _ hM => dgModuleExtension_homotopicallyProjective R (P) E projection hM
  have a := FunctorIso.postcomp
    (dgModuleResolvedInfinity_rawFactorIso R (C) (P) (J)).symm
    (dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
  have b := (dgModuleDerivedFunctor_underlyingIso R (P) E H hH).precomp
    (dgModuleResolvedInfinity R (C) (P) (J))
  have c := (dgModuleResolvedInfinity_inclusionIso R (C) (P) (J)
    (fun M => M.property.1)).postcomp (dgNerve.map H)
  have b' : FunctorIso
      (dgModuleResolvedInfinity R (C) (P) (J) ≫
        dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
      ((dgModuleResolvedInfinity R (C) (P) (J) ≫ dgNerve.map
        (dgFullSubcategoryInclusion R (RightModule R (P)) (dgModuleSemifreeProperty R (P)))) ≫
          dgNerve.map H) := by
    simpa only [dgNerve.map_comp, Category.assoc, dgModuleExtensionInfinity, H] using b
  simpa only [dgNerve.map_comp, Category.assoc] using a ≪≫ b' ≪≫ c

private lemma nativeFamilyNaturality {X Y Z : SSet.{w}}
    [Quasicategory Y] [Quasicategory Z] {f g : X ⟶ Y} {p q : Y ⟶ Z}
    (a : FunctorHom f g) (e : FunctorIso p q) :
    functorHomPostcomp f g p a ≫ (e.precomp g).hom =
      (e.precomp f).hom ≫ functorHomPostcomp f g q a := by
  rw [F2.functorIso_precomp_hom, F2.functorIso_precomp_hom]
  change (hoFunctor.map ((ihom X).map p)).toFunctor.map a ≫
      (hoFunctor.map ((pre g).app Z)).toFunctor.map e.hom =
    (hoFunctor.map ((pre f).app Z)).toFunctor.map e.hom ≫
      (hoFunctor.map ((ihom X).map q)).toFunctor.map a
  exact functorHom_whisker_exchange a e.hom

/-- 概要：共通 Perf 比較族は元の任意の全関手射に自然。
方針：同じ全比較と元射の二胞体交換則を適用する。
規約：元射の可逆性を仮定しない。使われ方：右軸から恒等への比較射の回収。 -/
lemma dgCellPerfectExtensionNativeFamily_naturality (projection : DGFunctor R (P) E)
    {X : SSet.{max (u + 1) v}} (f g : X ⟶ dgNerve R (C)) (a : FunctorHom f g) :
    functorHomPostcomp f g
        ((dgNerve.map (J) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫
          dgNerve.map (I)) a ≫
      ((dgCellPerfectExtensionNativeFamily R B E projection).precomp g).hom =
    ((dgCellPerfectExtensionNativeFamily R B E projection).precomp f).hom ≫
      functorHomPostcomp f g (dgNerve.map ((J).comp (dgModuleExtension R (P) E projection))) a := by
  exact nativeFamilyNaturality a (dgCellPerfectExtensionNativeFamily R B E projection)

end SerrePositivity.KST.SConstruction
