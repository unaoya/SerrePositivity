module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverPathStars
public import Mathlib.CategoryTheory.Category.Quiv

/-!
# 元の対称化した射列の自由 groupoid への評価

概要：元の対称化した射列と生成矢・逆向きの生成矢の商での値を固定する。
方針：元の自由 groupoid の商関手と元の逆射を使う。
規約：元の射列の商の表示を変更しない。
使われ方：被覆の持ち上げ終点と元の groupoid の矢の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def symmetricEvaluation : Paths (Quiver.Symmetrify Q) ⥤ Quiver.FreeGroupoid Q :=
  CategoryTheory.Quotient.functor (@Quiver.FreeGroupoid.redStep Q _)

lemma evaluation_positive {X Y : Q} (f : X ⟶ Y) :
    (symmetricEvaluation (Q := Q)).map f.toPosPath = (Quiver.FreeGroupoid.of Q).map f := rfl

lemma evaluation_negative {X Y : Q} (f : X ⟶ Y) :
    (symmetricEvaluation (Q := Q)).map f.toNegPath = inv ((Quiver.FreeGroupoid.of Q).map f) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

variable (A : Q)

def symmetricProjection :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) ⥤q Quiver.Symmetrify Q := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).symmetrify

def coverEvaluation :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    Paths (Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) ⥤ Quiver.FreeGroupoid Q := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact Cat.freeMap (symmetricProjection A) ⋙ symmetricEvaluation

lemma coverEvaluation_map (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ p : Quiver.Path (V := Quiver.Symmetrify (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)) x y,
      (coverEvaluation A).map p =
        symmetricEvaluation.map ((symmetricProjection A).mapPath p) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro p
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation
