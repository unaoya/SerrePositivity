module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar
public import SerrePositivity.EInfinity.Hammock.IndexedSum
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 元の二方向 bar の各行の両端因子の和による表示

概要：底の射列を固定した各行は、終点の左因子と始点の右因子の直積の依存和となる。
方針：元の全射列と両端ラベルの全単射を全単体次数で使う。
規約：元の底の射列の添字と全係数射を保持する。
使われ方：DK §9.5・10.6の元の二方向 bar の弱同値判定。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedBar
open CategoryTheory Opposite MonoidalCategory

variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ SSet.{u}) (G : W ⥤ SSet.{u})

def row (n : SimplexCategoryᵒᵖ) : SSet.{u} := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rows F G).flip.obj n

def endFactors (n : SimplexCategoryᵒᵖ) (c : ComposableArrows W n.unop.len) : SSet.{u} :=
  F.obj (op (c.obj (Fin.last n.unop.len))) ⊗ G.obj (c.obj 0)

def rowIso (n : SimplexCategoryᵒᵖ) :
    row F G n ≅ IndexedSum.space (endFactors F G n) :=
  NatIso.ofComponents
    (fun m => Equiv.toIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedLabelledChain.chainEquiv (F.flip.obj m) (G.flip.obj m) n.unop.len))
    (by intro m m' θ; apply ConcreteCategory.hom_ext; intro e; rfl)

variable {F G} {F' : Wᵒᵖ ⥤ SSet.{u}} {G' : W ⥤ SSet.{u}}

def flippedRowMap (α : F ⟶ F') (β : G ⟶ G') (n : SimplexCategoryᵒᵖ) :
    row F G n ⟶ row F' G' n := ((flipFunctor _ _ _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.rowMap α β)).app n

lemma rowIso_naturality (α : F ⟶ F') (β : G ⟶ G') (n : SimplexCategoryᵒᵖ) :
    flippedRowMap α β n ≫ (rowIso F' G' n).hom =
      (rowIso F G n).hom ≫ IndexedSum.map (fun c : ComposableArrows W n.unop.len =>
        α.app (op (c.obj (Fin.last n.unop.len))) ⊗ₘ β.app (c.obj 0)) := by
  ext m e
  rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedBar
