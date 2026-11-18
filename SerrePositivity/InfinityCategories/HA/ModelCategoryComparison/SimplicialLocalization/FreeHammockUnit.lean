module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.RelativeFixedUnit
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.HammockValueForward

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
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (X : C.category)

lemma freeHammockResolution_map {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X X).map θ =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ)
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FixedObjectDiagram.hammockOperator_eq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C)
    (fun θ X => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) θ X X

def freeHammockDiagonalUnit : 𝟙_ SSet.{u} ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonal C X X where
  app n := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    have hs := ConcreteCategory.congr_hom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C m X)).naturality θ) PUnit.unit
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C m X)).app m PUnit.unit =
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X X).obj m).map θ
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C m X)).app n PUnit.unit) at hs
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj m).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C m X)).app m PUnit.unit =
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X X).obj m).map θ
        (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X X).map θ).app n
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
            (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n PUnit.unit))
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution_map]
    have hr := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap_unit_point ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).map θ)
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_naturality C θ X) n
    exact hs.trans (congrArg (((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockResolution C X X).obj m).map θ) hr.symm)

lemma freeHammockDiagonalUnit_augmentation :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalUnit C X ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalAugmentation C X X =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit C.weakEquivalences X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation C X X).app n).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n PUnit.unit) = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockAugmentation_fixedColimitMap]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Relative.fixedColimitMap_unit_point _ _ _

lemma freeHammockDiagonalUnit_comparison :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalUnit C X ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockDiagonalComparison C X X =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationIdentity C X := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  cases p
  change (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeHammockLocalizationObjects C).homTransport n X X
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences.Q
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences.Q_inverts
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences
            (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)).app n PUnit.unit)) = 𝟙 _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint_identity, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Zigzag.Value.colimitValue_arrowPoint]
  change eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_localized C n X).symm ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolution C).obj n).weakEquivalences.Q.map (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject C n X)) ≫
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.freeResolutionObject_localized C n X) = 𝟙 _
  rw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
