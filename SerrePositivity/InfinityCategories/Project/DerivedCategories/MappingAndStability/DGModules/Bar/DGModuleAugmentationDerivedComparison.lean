module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Bar.DGModuleAugmentationHomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.Basic
/-!
概要：実 augmentation の準同型性から、同じ主導来像の自然同型を構成する。
方針：元の比較 cochain の境界式と同じ指定局所化を使う。
規約：入力の Small 性・元の出力の射影性を仮定しない。使われ方：一般 kernel の Morita 比較。
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
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onDerived :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E :=
  Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentation_onHomotopy R C E F)
    (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E)
/-- 同じ実 augmentation と元の主導来像の比較。 -/
lemma dgModuleAugmentation_onDerived_app_isIso
    (X : HomotopyCategory R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)) :
    IsIso ((dgModuleAugmentation_onDerived R C E F).app X) := by
  rcases X with ⟨X⟩
  change IsIso ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy R E ⋙ _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E).map
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) X).augmentation)
  exact (NatIso.isIso_map_iff (_root_.SerrePositivity.DifferentialGraded.moduleToHomotopyDerivedIso R E) _).mpr
    (_root_.SerrePositivity.DifferentialGraded.moduleToDerived_inverts R E _ (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) X).quasiIso)
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onDerivedIso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E := by
  letI : ∀ X, IsIso ((dgModuleAugmentation_onDerived R C E F).app X) :=
    dgModuleAugmentation_onDerived_app_isIso R C E F
  letI : IsIso (dgModuleAugmentation_onDerived R C E F) := NatIso.isIso_of_isIso_app _
  exact asIso (dgModuleAugmentation_onDerived R C E F)

/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleResolutionDerivedComparisonIso :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
      (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).onHomotopy ⋙
        _root_.SerrePositivity.DifferentialGraded.moduleHomotopyToDerivedClosed R E ≅
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).onHomotopy ⋙ F.onHomotopy ⋙
      moduleHomotopyToDerivedClosed R E := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationSource R C E F).onHomotopy =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
        (_root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R (_root_.SerrePositivity.DifferentialGraded.RightModule R E)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)).onHomotopy :=
    _root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_comp _ _
  have ht : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleAugmentationTarget R C E F).onHomotopy =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F).onHomotopy ⋙ F.onHomotopy :=
    _root_.SerrePositivity.DifferentialGraded.DGFunctor.onHomotopy_comp _ _
  have e := dgModuleAugmentation_onDerivedIso R C E F
  rw [hs, ht] at e
  exact (Functor.associator _ _ _).symm ≪≫ e ≪≫ Functor.associator _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
