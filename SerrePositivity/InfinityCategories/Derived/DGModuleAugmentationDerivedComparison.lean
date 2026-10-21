module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationHomotopyComparison
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onDerived :
    (dgModuleAugmentationSource R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E ⟶
      (dgModuleAugmentationTarget R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E :=
  Functor.whiskerRight (dgModuleAugmentation_onHomotopy R C E F)
    (moduleHomotopyToDerivedClosed R E)
/-- 同じ実 augmentation と元の主導来像の比較。 -/
lemma dgModuleAugmentation_onDerived_app_isIso
    (X : HomotopyCategory R (DGModuleFunctorResolutionObject R C E F)) :
    IsIso ((dgModuleAugmentation_onDerived R C E F).app X) := by
  rcases X with ⟨X⟩
  change IsIso ((moduleToHomotopy R E ⋙ moduleHomotopyToDerivedClosed R E).map
    (ForgetEnrichment.to (Complex R) X).augmentation)
  exact (NatIso.isIso_map_iff (moduleToHomotopyDerivedIso R E) _).mpr
    (moduleToDerived_inverts R E _ (ForgetEnrichment.to (Complex R) X).quasiIso)
/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleAugmentation_onDerivedIso :
    (dgModuleAugmentationSource R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E ≅
      (dgModuleAugmentationTarget R C E F).onHomotopy ⋙ moduleHomotopyToDerivedClosed R E := by
  letI : ∀ X, IsIso ((dgModuleAugmentation_onDerived R C E F).app X) :=
    dgModuleAugmentation_onDerived_app_isIso R C E F
  letI : IsIso (dgModuleAugmentation_onDerived R C E F) := NatIso.isIso_of_isIso_app _
  exact asIso (dgModuleAugmentation_onDerived R C E F)

/-- 同じ実 augmentation と元の主導来像の比較。 -/
def dgModuleResolutionDerivedComparisonIso :
    (dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
      (dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)).onHomotopy ⋙
        moduleHomotopyToDerivedClosed R E ≅
    (dgModuleFunctorResolutionSource R C E F).onHomotopy ⋙ F.onHomotopy ⋙
      moduleHomotopyToDerivedClosed R E := by
  have hs : (dgModuleAugmentationSource R C E F).onHomotopy =
      (dgModuleFunctorResolutionReplacement R C E F).onHomotopy ⋙
        (dgFullSubcategoryInclusion R (RightModule R E)
          (dgModuleSemifreeProperty R E)).onHomotopy :=
    DGFunctor.onHomotopy_comp _ _
  have ht : (dgModuleAugmentationTarget R C E F).onHomotopy =
      (dgModuleFunctorResolutionSource R C E F).onHomotopy ⋙ F.onHomotopy :=
    DGFunctor.onHomotopy_comp _ _
  have e := dgModuleAugmentation_onDerivedIso R C E F
  rw [hs, ht] at e
  exact (Functor.associator _ _ _).symm ≪≫ e ≪≫ Functor.associator _ _ _

end SerrePositivity.InfinityCategories
