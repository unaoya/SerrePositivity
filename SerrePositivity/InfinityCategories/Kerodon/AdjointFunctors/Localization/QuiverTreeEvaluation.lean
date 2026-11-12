module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation
public import Mathlib.Combinatorics.Quiver.Arborescence

/-!
# 対称化した部分木の元の自由 groupoid への評価

概要：部分 quiver の射列を元の対称射列として評価する。
方針：部分 quiver の包含と既存の商関手を合成する。
規約：正向きと逆向きの生成矢を同じ元の groupoid に送る。
使われ方：薄い自由 groupoid の生成 quiver の木性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEvaluation
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))

def inclusion : T ⥤q Quiver.Symmetrify Q where
  obj x := x
  map e := e.val

def evaluation : Paths T ⥤ Quiver.FreeGroupoid Q :=
  Cat.freeMap (inclusion T) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverEvaluation.symmetricEvaluation

lemma evaluation_positive {x y : Q} (f : x ⟶ y) (hf : f.toPos ∈ T x y) :
    (evaluation T).map (Quiver.Hom.toPath (⟨f.toPos, hf⟩ :
      (show T from x) ⟶ (show T from y))) = (Quiver.FreeGroupoid.of Q).map f := rfl

lemma evaluation_negative {x y : Q} (f : x ⟶ y) (hf : f.toNeg ∈ T y x) :
    (evaluation T).map (Quiver.Hom.toPath (⟨f.toNeg, hf⟩ :
      (show T from y) ⟶ (show T from x))) = inv ((Quiver.FreeGroupoid.of Q).map f) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEvaluation
