module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Unit
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# 元の縦射による一定 hammock 行の単体的ホモトピー

概要：固定語の実際の縦射から、一定行の単体写像間のホモトピーを作る。
方針：区間単体の単調写像を元の二対象の射列へ合成する。
規約：全単体作用素と元の両行を保持する。
使われ方：指定射の往復と単位を結ぶホモトピー。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

def rowMap (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y where
  app n := ↾fun _ => (Functor.const (Fin (n.unop.len + 1))).obj S
  naturality _ _ _ := rfl

def rowHomotopyMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    (𝟙_ SSet.{max u v}) ⊗ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y where
  app _ := ↾fun p => (SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor ⋙
    ComposableArrows.mk₁ f
  naturality _ _ _ := rfl

lemma rowHomotopyMap_zero {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    SSet.ι₀ ≫ rowHomotopyMap f = rowMap S := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma rowHomotopyMap_one {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    SSet.ι₁ ≫ rowHomotopyMap f = rowMap T := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.ext (fun _ => rfl)

def rowHomotopy {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} (f : S ⟶ T) :
    SSet.Homotopy (rowMap S) (rowMap T) where
  h := rowHomotopyMap f
  h₀ := rowHomotopyMap_zero f
  h₁ := rowHomotopyMap_one f
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagRowHomotopy
