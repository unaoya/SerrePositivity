module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationDerivedComparison
/-!
概要：実分解圏の入力射影の H⁰ 同値から、出力分解の主導来比較を元の入力へ戻す。
方針：実対象上の全射と全 Hom の準同型性、同じ augmentation の自然同型を使う。
規約：元の出力の射影性を追加しない。使われ方：一般 kernel 作用の主導来比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
lemma dgModuleFunctorResolutionSource_onHomotopy_isEquivalence :
    (dgModuleFunctorResolutionSource R C E F).onHomotopy.IsEquivalence := by
  let P := dgModuleFunctorResolutionSource R C E F
  have hq : HomQuasiIso P := dgModuleFunctorResolutionSource_homQuasiIso R C E F
  change P.onHomotopy.IsEquivalence
  refine { full := P.onHomotopy_full_of_homQuasiIso hq
           faithful := P.onHomotopy_faithful_of_homQuasiIso hq
           essSurj := ⟨?_⟩ }
  rintro ⟨Y⟩
  obtain ⟨X, hX⟩ := dgModuleFunctorResolutionSource_obj_surjective R C E F
    (ForgetEnrichment.to (Complex R) Y)
  refine ⟨(toHomotopy R (DGModuleFunctorResolutionObject R C E F)).obj
    (ForgetEnrichment.of (Complex R) X), ⟨eqToIso ?_⟩⟩
  change (toHomotopy R C).obj (ForgetEnrichment.of (Complex R) X.source) =
    (toHomotopy R C).obj Y
  change X.source = ForgetEnrichment.to (Complex R) Y at hX
  rw [hX]
  rfl

/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleResolutionSourceHomotopyEquivalence :
    HomotopyCategory R (DGModuleFunctorResolutionObject R C E F) ≌ HomotopyCategory R C := by
  letI := dgModuleFunctorResolutionSource_onHomotopy_isEquivalence R C E F
  exact (dgModuleFunctorResolutionSource R C E F).onHomotopy.asEquivalence
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleOutputResolutionClassical : HomotopyCategory R C ⥤ DerivedModuleCategory R E :=
  (dgModuleResolutionSourceHomotopyEquivalence R C E F).inverse ⋙
    (dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
      (dgFullSubcategoryInclusion R (RightModule R E)
        (dgModuleSemifreeProperty R E)).onHomotopy ⋙
        moduleHomotopyToDerivedClosed R E
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleOutputResolutionClassicalComparisonIso :
    dgModuleOutputResolutionClassical R C E F ≅
      F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E := by
  let e := dgModuleResolutionSourceHomotopyEquivalence R C E F
  have h := Functor.isoWhiskerLeft e.inverse (dgModuleResolutionDerivedComparisonIso R C E F)
  exact h ≪≫ (Functor.associator e.inverse
      (dgModuleFunctorResolutionSource R C E F).onHomotopy
      (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E)).symm ≪≫
    Functor.isoWhiskerRight e.counitIso (F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E) ≪≫
    Functor.leftUnitor _

end SerrePositivity.InfinityCategories
