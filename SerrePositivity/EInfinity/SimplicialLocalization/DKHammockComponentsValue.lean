module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockAugmentationValue
public import SerrePositivity.EInfinity.SimplicialLocalization.DKHammockCoefficientComparison
public import SerrePositivity.EInfinity.SimplicialLocalization.ComponentsEquivalence
public import SerrePositivity.EInfinity.Hammock.AnodyneComponents

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
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock SerrePositivity.SimplicialModel Opposite
open scoped Simplicial

lemma dkHammockComparisonIso_components_value (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (z : SSet.π₀ (localizationHom C X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents
        (Zigzag.Value.reducedValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y)
        ((AnodyneComponents.iso (dkHammockComparisonIso C X Y)).hom z) =
      localizationHomPiZeroEquiv C X Y z := by
  have hi := anodyneQ_map_isIso_of_weak (freeHammockDiagonalComparison C X Y)
    (freeHammockDiagonalComparison_isWeakHomotopyEquivalence C X Y)
  obtain ⟨t, rfl⟩ := (PiZeroLocalization.piZero_bijective
    (freeHammockDiagonalComparison C X Y) hi).surjective z
  obtain ⟨p, rfl⟩ := SSet.π₀.mk_surjective t
  have h := ConcreteCategory.congr_hom
    (AnodyneComponents.iso_fac (dkHammockComparisonIso C X Y)
      (freeHammockDiagonalComparison C X Y) (freeHammockDiagonalReduction C X Y)
      (dkHammockComparisonIso_fac C X Y)) (SSet.π₀.mk p)
  change (AnodyneComponents.iso (dkHammockComparisonIso C X Y)).hom
      (SSet.mapπ₀ (freeHammockDiagonalComparison C X Y) (SSet.π₀.mk p)) =
    SSet.mapπ₀ (freeHammockDiagonalReduction C X Y) (SSet.π₀.mk p) at h
  rw [h]
  change (Zigzag.Value.reducedValue C.weakEquivalences.Q
      C.weakEquivalences.Q_inverts X Y).app (op ⦋0⦌)
        ((freeHammockDiagonalReduction C X Y).app (op ⦋0⦌) p) =
    (localizationHomAugmentation C X Y).app (op ⦋0⦌)
      ((freeHammockDiagonalComparison C X Y).app (op ⦋0⦌) p)
  exact congrArg (fun m => m.app (op ⦋0⦌) p) (freeHammockDiagonalReduction_value C X Y)

end SerrePositivity.EInfinity.SimplicialLocalization
