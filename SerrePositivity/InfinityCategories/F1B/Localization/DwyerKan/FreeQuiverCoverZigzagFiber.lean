module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverZigzagHorizontal
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# 元の全指定 zigzag の値を固定した全部分圏

概要：元の自由 groupoid の射を値とする zigzag を全縦射を含めて扱う。
方針：既存の元の値の等式による全部分圏とし、終点ラベルを回収する。
規約：値の等式だけで制限し、元の列や縦射は変更しない。
使われ方：固定端点の被覆上の zigzag への持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def zigzagValueProperty :
    ObjectProperty (Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :=
  fun S => Zigzag.Value.value positiveEvaluation positiveEvaluation_inverts_top S = β

abbrev ZigzagValueFiber := (zigzagValueProperty A w Y β).FullSubcategory

def fiberEndpoint : Vertex A := ⟨Y, β⟩

variable {w Y β}

lemma zigzagPrefix_last_heq_value
    (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    HEq (zigzagPrefix A S (Fin.last w.length))
      (Zigzag.Value.value positiveEvaluation positiveEvaluation_inverts_top S) := by
  have he : zigzagPrefix A S (Fin.last w.length) ≫
      eqToHom (congrArg positiveEvaluation.obj S.last) =
        Zigzag.Value.value positiveEvaluation positiveEvaluation_inverts_top S :=
    Category.assoc _ _ _
  exact (comp_eqToHom_heq _ _).symm.trans (heq_of_eq he)

lemma zigzagVertex_last (S : ZigzagValueFiber A w Y β) :
    zigzagVertex A S.obj (Fin.last w.length) = fiberEndpoint A Y β := by
  apply Vertex.ext S.obj.last
  exact (zigzagPrefix_last_heq_value A S.obj).trans (heq_of_eq S.property)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
