module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleAugmentationDerivedComparison
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
lemma dgModuleFunctorResolutionSource_onHomotopy_isEquivalence :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).onHomotopy.IsEquivalence := by
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F
  have hq : HomQuasiIso P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_homQuasiIso R C E F
  change P.onHomotopy.IsEquivalence
  refine { full := P.onHomotopy_full_of_homQuasiIso hq
           faithful := P.onHomotopy_faithful_of_homQuasiIso hq
           essSurj := ⟨?_⟩ }
  rintro ⟨Y⟩
  obtain ⟨X, hX⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_obj_surjective R C E F
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Y)
  refine ⟨(toHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)).obj
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X), ⟨eqToIso ?_⟩⟩
  change (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.source) =
    (_root_.SerrePositivity.DifferentialGraded.toHomotopy R C).obj Y
  change X.source = ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) Y at hX
  rw [hX]
  rfl

/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleResolutionSourceHomotopyEquivalence :
    HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F) ≌ HomotopyCategory R C := by
  letI := dgModuleFunctorResolutionSource_onHomotopy_isEquivalence R C E F
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).onHomotopy.asEquivalence
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleOutputResolutionClassical : _root_.SerrePositivity.DifferentialGraded.HomotopyCategory R C ⥤ DerivedModuleCategory R E :=
  (dgModuleResolutionSourceHomotopyEquivalence R C E F).inverse ⋙
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
      (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).onHomotopy ⋙
        _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E
/-- 実入力射影の同値を使い、元の出力分解の主導来比較を入力側へ戻す。 -/
def dgModuleOutputResolutionClassicalComparisonIso :
    dgModuleOutputResolutionClassical R C E F ≅
      F.onHomotopy ⋙ moduleHomotopyToDerivedClosed R E := by
  let e := dgModuleResolutionSourceHomotopyEquivalence R C E F
  have h := Functor.isoWhiskerLeft e.inverse (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionDerivedComparisonIso R C E F)
  exact h ≪≫ (Functor.associator e.inverse
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).onHomotopy
      (F.onHomotopy ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E)).symm ≪≫
    Functor.isoWhiskerRight e.counitIso (F.onHomotopy ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E) ≪≫
    Functor.leftUnitor _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
