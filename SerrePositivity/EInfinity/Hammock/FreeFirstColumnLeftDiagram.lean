module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryEqToHom
public import SerrePositivity.EInfinity.Hammock.FreeFirstColumnHomWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramVertexCoefficientMap

/-!
# 元の自由解像の左係数と残りの語の圏図式

概要：元の左係数の図式は、同じ指定対象を始点とする元の残りの語の図式と同型。
方針：元の作用素の像と境界の等式射を同じ固定端点の関手に戻す。
規約：元の全相対作用素と全縦射を保持する。
使われ方：DK5.7の帰納仮定を元の左係数へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
open Zigzag.FirstBoundary TwoSidedDiagram.FixedVertices
variable (C : RelativeCategory.{u}) (w : Word) (X Y Z : C.category)
def freeFirstLeftCategoryDiagramIso :
    leftDiagram (D := freeForwardForwardDiagram C w X Y) (freeFirstMarkedObjectEquiv C)
      (freeFirstMarkedObjectEquiv_naturality C w X Y) Z ≅
    FixedObjectDiagram.zigzagDiagram (freeResolution C) (freeResolutionObject C)
      (fun θ X => freeResolutionObject_naturality C θ X) (Word.cons .forward w) Z Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro n m θ
    apply Cat.Hom.ext
    change (Zigzag.Relative.fixedFunctor ((freeResolution C).map θ) rfl
        (freeResolutionObject_naturality C θ Y) ⋙
      forwardFunctor ((eqToHom (congrArg op
        (freeFirstMarkedObjectEquiv_naturality C w X Y θ Z))).unop).hom) ⋙ 𝟭 _ =
      (𝟭 _) ⋙ Zigzag.Relative.fixedFunctor ((freeResolution C).map θ)
        (freeResolutionObject_naturality C θ Z) (freeResolutionObject_naturality C θ Y)
    rw [CategoryTheory.Functor.comp_id, CategoryTheory.Functor.id_comp]
    have hZ : ((eqToHom (congrArg op
        (freeFirstMarkedObjectEquiv_naturality C w X Y θ Z))).unop).hom =
          eqToHom (freeResolutionObject_naturality C θ Z).symm := by
      rw [eqToHom_unop]
      exact marked_eqToHom_hom (C := (freeResolution C).obj m) _
    rw [hZ, forwardFunctor_eqToHom (freeResolutionObject_naturality C θ Z)]
    rfl)
end SerrePositivity.EInfinity.Hammock.FirstColumn
