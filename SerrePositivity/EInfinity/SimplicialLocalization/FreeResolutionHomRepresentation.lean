module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeResolutionHomContraction

/-!
# 元の選択対象による Hom への収縮の移送

概要：標準生成対象による追加退化の結論を元の固定 Hom augmentation 自身へ戻す。
方針：同じ二つの対象表示の等式を使う単体同型と augmentation の可換式を構成する。
規約：元の augmentation を別の弱同値で置き換えない。
使われ方：DK ホモトピー補題2.4に使う元の Hom の弱比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X Y : C.category)

def freeResolutionHomRepresentationIso :
    freeResolutionHom C X Y ≅ freeResolutionGeneratorHom C X Y where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (freeResolutionUnderlyingDiagram C)
    (freeResolutionUnderlyingDiagram C) (freeResolutionObject C) (freeResolutionHomObject C)
    (fun θ X => freeResolutionObject_naturality C θ X)
    (fun θ X => freeResolutionHomObject_naturality C θ X) (𝟙 _) id
    (fun n X => freeResolutionObject_eq_homObject C n X) X Y
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans (freeResolutionUnderlyingDiagram C)
    (freeResolutionUnderlyingDiagram C) (freeResolutionHomObject C) (freeResolutionObject C)
    (fun θ X => freeResolutionHomObject_naturality C θ X)
    (fun θ X => freeResolutionObject_naturality C θ X) (𝟙 _) id
    (fun n X => (freeResolutionObject_eq_homObject C n X).symm) X Y
  hom_inv_id := by
    ext n f
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap]
  inv_hom_id := by
    ext n f
    simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientNatTrans, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality.coefficientMap]

lemma freeResolutionHomRepresentationIso_augmentation :
    (freeResolutionHomRepresentationIso C X Y).hom ≫
      freeResolutionGeneratorHomAugmentation C X Y = freeResolutionHomAugmentation C X Y := by
  ext n f
  change (eqToHom _ ≫ ((freeResolutionAugmentationNatTrans C).app n).functor.map
    (eqToHom _ ≫ f ≫ eqToHom _) ≫ eqToHom _) =
      eqToHom _ ≫ ((freeResolutionAugmentationNatTrans C).app n).functor.map f ≫ eqToHom _
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

lemma freeResolutionHomAugmentation_isWeakHomotopyEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence
      (freeResolutionHomAugmentation C X Y) := by
  rw [← freeResolutionHomRepresentationIso_augmentation]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (freeResolutionHomRepresentationIso C X Y)).isWeakHomotopyEquivalence.comp
      (freeResolutionGeneratorHomAugmentation_isWeakHomotopyEquivalence C X Y)

end SerrePositivity.EInfinity.SimplicialLocalization
