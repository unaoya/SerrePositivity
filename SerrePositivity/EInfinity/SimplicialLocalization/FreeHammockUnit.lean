module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.EInfinity.Hammock.RelativeFixedUnit
public import SerrePositivity.EInfinity.Hammock.HammockValueForward

/-!
# 元の自由 hammock 対角の空語の単位

概要：元の各自由次数の実単位点を同じ対角の単体写像へ束ねる。
方針：元の相対作用素の固定端点の単位保存と内側の全作用素の自然性を使う。
規約：原圏の恒等射の自由な生成射へ置き換えない。
使われ方：左右比較を同じ単位を保つ豊穣関手にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory MonoidalCategory Hammock
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

lemma freeHammockResolution_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (freeHammockResolution C X X).map θ =
      Relative.fixedColimitMap ((freeResolution C).map θ)
        (freeResolutionObject_naturality C θ X) (freeResolutionObject_naturality C θ X) :=
  FixedObjectDiagram.hammockOperator_eq (freeResolution C) (freeResolutionObject C)
    (fun θ X => freeResolutionObject_naturality C θ X) θ X X

def freeHammockDiagonalUnit : 𝟙_ SSet.{u} ⟶ freeHammockDiagonal C X X where
  app n := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
    (freeResolutionObject C n X)).app n
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    have hs := ConcreteCategory.congr_hom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj m).weakEquivalences
        (freeResolutionObject C m X)).naturality θ) PUnit.unit
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj m).weakEquivalences
        (freeResolutionObject C m X)).app m PUnit.unit =
      ((freeHammockResolution C X X).obj m).map θ
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj m).weakEquivalences
          (freeResolutionObject C m X)).app n PUnit.unit) at hs
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj m).weakEquivalences
        (freeResolutionObject C m X)).app m PUnit.unit =
      ((freeHammockResolution C X X).obj m).map θ
        (((freeHammockResolution C X X).map θ).app n
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
            (freeResolutionObject C n X)).app n PUnit.unit))
    rw [freeHammockResolution_map]
    have hr := Relative.fixedColimitMap_unit_point ((freeResolution C).map θ)
      (freeResolutionObject_naturality C θ X) n
    exact hs.trans (congrArg (((freeHammockResolution C X X).obj m).map θ) hr.symm)

lemma freeHammockDiagonalUnit_augmentation :
    freeHammockDiagonalUnit C X ≫ freeHammockDiagonalAugmentation C X X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit C.weakEquivalences X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  change ((freeHammockAugmentation C X X).app n).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
        (freeResolutionObject C n X)).app n PUnit.unit) = _
  rw [freeHammockAugmentation_fixedColimitMap]
  exact Relative.fixedColimitMap_unit_point _ _ _

lemma freeHammockDiagonalUnit_comparison :
    freeHammockDiagonalUnit C X ≫ freeHammockDiagonalComparison C X X =
      localizationIdentity C X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  change (freeHammockLocalizationObjects C).homTransport n X X
      ((Zigzag.Value.colimitValue ((freeResolution C).obj n).weakEquivalences.Q
        ((freeResolution C).obj n).weakEquivalences.Q_inverts
        (freeResolutionObject C n X) (freeResolutionObject C n X)).app n
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((freeResolution C).obj n).weakEquivalences
            (freeResolutionObject C n X)).app n PUnit.unit)) = 𝟙 _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity, Zigzag.Value.colimitValue_arrowPoint]
  change eqToHom (freeResolutionObject_localized C n X).symm ≫
      ((freeResolution C).obj n).weakEquivalences.Q.map (𝟙 (freeResolutionObject C n X)) ≫
      eqToHom (freeResolutionObject_localized C n X) = 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

end SerrePositivity.EInfinity.SimplicialLocalization
