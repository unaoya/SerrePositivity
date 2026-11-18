module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockAugmentationValue
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.DKHammockCoefficientComparison
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ComponentsEquivalence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents

/-!
# native DK/hammock 高次比較の誘導する π₀ と元の augmentation

概要：元の高次比較を π₀ へ送り、以前の局所化 Hom 同値と一致させる。
方針：同じ左右の因子化と元の右比較の π₀ の全射性で全類を回収する。
規約：元の比較同型・全語・同じ通常の局所化を保持する。
使われ方：実 DK/Map^h 比較の以前の π₀ 同値との一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock _root_.SerrePositivity.SimplicialModel _root_.Opposite
open scoped _root_.Simplicial

lemma dkHammockComparisonIso_components_value (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHom C X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y)
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y)).hom z) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomPiZeroEquiv C X Y z := by
  have hi := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.anodyneQ_map_isIso_of_weak (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  obtain ⟨t, rfl⟩ := (PiZeroLocalization.piZero_bijective
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) hi).surjective z
  obtain ⟨p, rfl⟩ := SSet.π₀.mk_surjective t
  have h := ConcreteCategory.congr_hom
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso_fac (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso_fac C X Y)) (SSet.π₀.mk p)
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.AnodyneComponents.iso (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.dkHammockComparisonIso C X Y)).hom
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y) (SSet.π₀.mk p)) =
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y) (SSet.π₀.mk p) at h
  rw [h]
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.reducedValue C.weakEquivalences.Q
      C.weakEquivalences.Q_inverts X Y).app (op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction C X Y).app (op ⦋0⦌) p) =
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationHomAugmentation C X Y).app (op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X Y).app (op ⦋0⦌) p)
  exact congrArg (fun m => m.app (op ⦋0⦌) p) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalReduction_value C X Y)

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
