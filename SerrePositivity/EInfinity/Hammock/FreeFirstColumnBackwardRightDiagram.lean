module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardEqToHom
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnBackwardHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap

/-!
# 元の自由解像の右係数と残りの語の圏図式

概要：元の右係数の図式は、同じ指定対象を始点とする元の残りの語の図式と同型。
方針：元の作用素の像と境界の等式射を同じ固定端点の関手に戻す。
規約：元の全相対作用素と全縦射を保持する。
使われ方：DK5.7の帰納仮定を元の右係数へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
open TwoSidedDiagram.FixedVertices
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y Z : C.category)
def freeBackwardFirstRightCategoryDiagramIso :
    rightDiagram (D := freeBackwardBackwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectZigzagDiagram.zigzagDiagram (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) Z Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply Cat.Hom.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolution C).map θ) rfl
        (freeResolutionObject_naturality C θ Y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps.backwardFunctor
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y θ Z)).hom
        (eqToHom (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y θ Z)).property) ⋙ 𝟭 _ =
      (𝟭 _) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor ((freeResolution C).map θ)
        (freeResolutionObject_naturality C θ Z) (freeResolutionObject_naturality C θ Y)
    rw [CategoryTheory.Functor.comp_id, CategoryTheory.Functor.id_comp]
    have hZ : (eqToHom (freeBackwardFirstMarkedObjectEquiv_naturality C w X Y θ Z)).hom =
          eqToHom (freeResolutionObject_naturality C θ Z) :=
      marked_eqToHom_hom (C := (freeResolution C).obj m) _
    simp only [hZ]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardFunctor_eqToHom (freeResolutionObject_naturality C θ Z)]
    rfl)
end SerrePositivity.EInfinity.Hammock.FirstColumn
