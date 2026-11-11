module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordEmptyFiber
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordPlateauColumn

/-!
# 元の zigzag の恒等列

概要：隣接頂点の等式と元の同じ恒等移送であることを、恒等列の条件として束ねる。
方針：列の向きに応じて元の隣接頂点の等式を戻す。
規約：局所化後だけの恒等性ではなく、元の対象と射の等式。
使われ方：語の包含の対象の像の特徴付けと proper 性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

/-- 隣接二点の等式を元の列の向きへ移す。 -/
lemma Direction.endpointsEq {I : Type*} {A : Sort*} (V : I → A) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : I) (h : V p = V q) : V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.source d p q) = V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.target d p q) := by
  cases d
  · exact h
  · exact h.symm

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 元の隣接頂点と元の射が、等式による同じ恒等列である条件。 -/
structure IdentityColumn (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y) (j : Fin b.length) : Prop where
  vertex_eq : R.vertex j.castSucc = R.vertex j.succ
  arrow_eq : R.arrow j = eqToHom
    (Direction.endpointsEq R.vertex (b.direction j) j.castSucc j.succ vertex_eq)

/-- 指定列の像の外が全て元の恒等列である条件。 -/
def IdentityOutside (f : a ⟶ b) (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y) : Prop :=
  ∀ j : Fin b.length, (∀ i : Fin a.length, f.orderHom i ≠ j) → IdentityColumn R j

/-- 同じ切断の列には、元の列の像が存在しない。 -/
lemma Word.Hom.no_image_of_cut_eq (f : a ⟶ b) (j : Fin b.length)
    (h : f.cut j.castSucc = f.cut j.succ) : ∀ i : Fin a.length, f.orderHom i ≠ j := by
  intro i hi
  have hh := (f.fiber_iff j i).2 hi
  rw [h] at hh
  exact (not_lt_of_ge hh.1) hh.2

/-- 元の語の遷移の像の外は、同じ元の恒等列。 -/
lemma WordAction.identityOutside_obj [W.IsMultiplicative] (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    IdentityOutside f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) := by
  intro j hj
  have h := f.cut_empty_fiber j hj
  refine ⟨congrArg S.vertex h, ?_⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column_eqToHom_of_cut_eq f S j h (f.cut_source_target_of_eq j h)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
