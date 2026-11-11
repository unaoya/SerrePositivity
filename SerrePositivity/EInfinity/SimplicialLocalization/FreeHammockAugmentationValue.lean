module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.EInfinity.SimplicialLocalization.HomAugmentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueComparison
public import SerrePositivity.EInfinity.Hammock.HammockValueComposition

/-!
# 元の自由 hammock と DK augmentation の同じ局所化への評価

概要：左右の実比較を、元の通常の局所化への同じ評価で結ぶ。
方針：各自由次数の全語の値を比較し、共同全射性で元の対角へ移す。
規約：元の augmentation・元の対象移送・全語と全単体を保持する。
使われ方：実 DK/Map^h 高次比較の誘導する π₀ の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock

lemma freeHammockValue_augmentation (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : SimplexCategoryᵒᵖ)
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag ((freeResolution C).obj n).weakEquivalences w
      (freeResolutionObject C n X) (freeResolutionObject C n Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value C.weakEquivalences.Q C.weakEquivalences.Q_inverts
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
          (freeResolutionObject_augmentation C n X)
          (freeResolutionObject_augmentation C n Y)).obj S) =
      (localizationHomAugmentation C X Y).app n
        ((freeHammockLocalizationObjects C).value n S) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value C.weakEquivalences.Q C.weakEquivalences.Q_inverts
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X)
        (freeResolutionObject_augmentation C n Y)).obj S) =
    eqToHom (localizedFreeResolutionAugmentation_object C n X).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((freeResolutionAugmentationNatTrans C).app n)).map
        ((freeHammockLocalizationObjects C).value n S) ≫
      eqToHom (localizedFreeResolutionAugmentation_object C n Y)
  apply eq_of_heq
  dsimp only [FixedObjectDiagram.LocalizationObjects.value]
  simp only [Functor.map_comp, eqToHom_map, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_fixed_comparison ((freeResolutionAugmentationNatTrans C).app n)
    ((freeResolution C).obj n).weakEquivalences.Q
    ((freeResolution C).obj n).weakEquivalences.Q_inverts
    C.weakEquivalences.Q C.weakEquivalences.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap ((freeResolutionAugmentationNatTrans C).app n))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac ((freeResolutionAugmentationNatTrans C).app n))
    (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) S

lemma freeHammockDiagonalComparison_augmentation_value
    (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonalComparison C X Y ≫ localizationHomAugmentation C X Y =
      freeHammockDiagonalAugmentation C X Y ≫
        Zigzag.Value.colimitValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  obtain ⟨w, σ, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram ((freeResolution C).obj n).weakEquivalences
      (freeResolutionObject C n X) (freeResolutionObject C n Y)) n p
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution C).obj n).weakEquivalences
    (freeResolutionObject C n X) (freeResolutionObject C n Y) w).app n σ = p at hp
  cases hp
  have hr := congrArg (fun m => m.app n σ) (freeHammockHomComparison_fac C X Y n w)
  have hl := congrArg (fun m => m.app n σ)
    (Relative.fixedColimitMap_inclusion ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y) w)
  change ((freeHammockHomComparison C X Y).app n).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X) (freeResolutionObject C n Y) w).app n σ) =
    (freeHammockLocalizationObjects C).value n (σ.obj 0) at hr
  change (Relative.fixedColimitMap ((freeResolutionAugmentationNatTrans C).app n)
      (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y)).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X) (freeResolutionObject C n Y) w).app n σ) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion C.weakEquivalences X Y w).app n
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X) (freeResolutionObject_augmentation C n Y)) at hl
  change (localizationHomAugmentation C X Y).app n
      (((freeHammockHomComparison C X Y).app n).app n _) =
    (Zigzag.Value.colimitValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y).app n
      (((freeHammockAugmentation C X Y).app n).app n _)
  rw [freeHammockAugmentation_fixedColimitMap]
  exact (congrArg ((localizationHomAugmentation C X Y).app n) hr).trans
    ((freeHammockValue_augmentation C X Y w n (σ.obj 0)).symm.trans
      ((Zigzag.Value.colimitValue_inclusion_app C.weakEquivalences.Q
      C.weakEquivalences.Q_inverts X Y w
      (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolutionAugmentationNatTrans C).app n)
        (freeResolutionObject_augmentation C n X)
        (freeResolutionObject_augmentation C n Y))).symm.trans
          (congrArg ((Zigzag.Value.colimitValue C.weakEquivalences.Q
            C.weakEquivalences.Q_inverts X Y).app n) hl).symm))

lemma freeHammockDiagonalReduction_value (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category) :
    freeHammockDiagonalReduction C X Y ≫
        Zigzag.Value.reducedValue C.weakEquivalences.Q C.weakEquivalences.Q_inverts X Y =
      freeHammockDiagonalComparison C X Y ≫ localizationHomAugmentation C X Y := by
  rw [freeHammockDiagonalComparison_augmentation_value]
  simp only [freeHammockDiagonalReduction, Zigzag.Value.reducedValue,
    ← reducedColimitIso_inv, Category.assoc, Iso.hom_inv_id_assoc]

end SerrePositivity.EInfinity.SimplicialLocalization
