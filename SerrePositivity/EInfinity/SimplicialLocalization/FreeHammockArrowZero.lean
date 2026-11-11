module

public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockComposition
public import SerrePositivity.EInfinity.Hammock.HammockValueForward

/-!
# 元の射を自由 hammock 対角の零単体へ持ち上げる

概要：元の一文字の自由射を共通始域の同じ一列へ送る。
方針：元の自由対象の表示を移し、元の局所化評価で生成射を回収する。
規約：元の射と元の両端点を保持する。
使われ方：DK と hammock の比較の元の射への整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Opposite Hammock
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {X Y : C.category}

def freeResolutionArrowZero (f : X ⟶ Y) :
    freeResolutionObject C (op ⦋0⦌) X ⟶ freeResolutionObject C (op ⦋0⦌) Y :=
  eqToHom (freeResolutionObject_generator C 0 X) ≫ (Paths.of C.category).map f ≫
    eqToHom (freeResolutionObject_generator C 0 Y).symm

def freeHammockArrowZero (f : X ⟶ Y) : (freeHammockDiagonal C X Y) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint ((freeResolution C).obj (op ⦋0⦌)).weakEquivalences
    (freeResolutionArrowZero C f) (op ⦋0⦌)

lemma freeHammockArrowZero_comparison (f : X ⟶ Y) :
    (freeHammockDiagonalComparison C X Y).app (op ⦋0⦌) (freeHammockArrowZero C f) =
      localizationArrowZero C f := by
  change eqToHom (freeResolutionObject_localized C (op ⦋0⦌) X).symm ≫
      (Zigzag.Value.colimitValue ((freeResolution C).obj (op ⦋0⦌)).weakEquivalences.Q
        ((freeResolution C).obj (op ⦋0⦌)).weakEquivalences.Q_inverts _ _).app (op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint _ (freeResolutionArrowZero C f) (op ⦋0⦌)) ≫
      eqToHom (freeResolutionObject_localized C (op ⦋0⦌) Y) = localizationArrowZero C f
  rw [Zigzag.Value.colimitValue_arrowPoint]
  dsimp only [freeResolutionArrowZero, localizationArrowZero]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
