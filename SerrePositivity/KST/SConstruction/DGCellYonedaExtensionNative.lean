module
public import SerrePositivity.KST.SConstruction.DGCellPerfectExtensionNativeFamily
public import SerrePositivity.KST.SConstruction.DGFunctorCoherence
public import SerrePositivity.InfinityCategories.Derived.DGPerfectYoneda
public import SerrePositivity.InfinityCategories.Derived.DGModuleExtensionYonedaNerveIso
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
local notation "YP" => dgPerfectYoneda R (P)
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)

/-- 概要：元 Yoneda の native 延長の全包含像は同じ元実 dg 延長。
方針：既存の同じ全 Perf 比較族を元 perfect Yoneda へ前合成する。
規約：新しい分解・比較を選ばない。使われ方：同じ商射影の元 Yoneda 回収の第一因子。 -/
def dgCellYonedaExtensionNativeComparison (projection : DGFunctor R (P) E) :
    FunctorIso (((dgNerve.map (Y) ≫ (ρ)) ≫ (dgModuleExtensionInfinity R (P) E projection)) ≫ dgNerve.map (I))
      (dgNerve.map ((Y).comp (dgModuleExtension R (P) E projection))) := by
  let e := (dgCellPerfectExtensionNativeFamily R B E projection).precomp (dgNerve.map (YP))
  have hj : dgNerve.map (YP) ≫ dgNerve.map (J) = dgNerve.map (Y) :=
    (dgNerve.map_comp (YP) (J)).symm.trans
      (congrArg dgNerve.map (dgPerfectYoneda_inclusion R (P)))
  have hs : dgNerve.map (YP) ≫
      ((dgNerve.map (J) ≫ (ρ)) ≫ (dgModuleExtensionInfinity R (P) E projection) ≫ dgNerve.map (I)) =
        ((dgNerve.map (Y) ≫ (ρ)) ≫ (dgModuleExtensionInfinity R (P) E projection)) ≫ dgNerve.map (I) := by
    simpa only [Category.assoc] using congrArg
      (fun f => ((f ≫ (ρ)) ≫ (dgModuleExtensionInfinity R (P) E projection)) ≫ dgNerve.map (I)) hj
  have ht : dgNerve.map (YP) ≫ dgNerve.map ((J).comp (dgModuleExtension R (P) E projection)) =
      dgNerve.map ((Y).comp (dgModuleExtension R (P) E projection)) := by
    rw [← dgNerve.map_comp, ← strictDGFunctor_comp_assoc, dgPerfectYoneda_inclusion]
  exact F2.functorIsoOfEq e hs ht

/-- 概要：元 Yoneda の native 延長は同じ指定射の元 Yoneda と全比較される。
方針：同じ全 Perf 前合成比較と D 正本の全代表延長比較を合成する。
規約：元の全自然変換を保持。使われ方：同じ resolved 射影の全回収。 -/
def dgCellYonedaProjectionNativeComparison (projection : DGFunctor R (P) E) :
    FunctorIso (((dgNerve.map (Y) ≫ (ρ)) ≫ (dgModuleExtensionInfinity R (P) E projection)) ≫ dgNerve.map (I))
      (dgNerve.map (projection.comp (dgYoneda R E))) :=
  (dgCellYonedaExtensionNativeComparison R B E projection).trans
    (dgModuleFunctorIsoOfStrictNatTrans R E (dgModuleExtensionYonedaStrict R (P) E projection)
      (fun x => (dgModuleExtensionRepresentableIso R (P) E projection x).hom)
      (fun _ => rfl)
      (fun x => (dgModuleExtensionRepresentableIso R (P) E projection x).isIso_hom))
end SerrePositivity.KST.SConstruction
