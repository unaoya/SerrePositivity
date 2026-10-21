module

public import SerrePositivity.EInfinity.Hammock.HammockValueComposition
public import SerrePositivity.EInfinity.Hammock.Unit

/-!
# 元の forward 一列の局所化評価の回収

概要：元の射の一定単体を評価すると、同じ反転関手の射像を得る。
方針：元の長さ一の値の射列の唯一の隣接列を回収する。
規約：元の恒等射を表す一文字の列も含める。
使われ方：元の非指定生成矢を含む全因子列の評価。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.Value
open CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)

omit [W.IsMultiplicative] in
lemma value_forward {X Y : C} (p : X ⟶ Y) :
    value L hL (ForwardZigzag.obj (W := W) p) = L.map p := by
  unfold value
  simp only [ForwardZigzag.obj, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (path L hL (ForwardZigzag.obj (W := W) p)).map
    (homOfLE (Fin.castSucc_le_succ (0 : Fin 1))) = _
  rw [path_map_adjacent, edge_forward L hL _ _ rfl]
  apply congrArg L.map
  exact eq_of_heq (Direction.forward_arrow_heq (ForwardZigzag.obj (W := W) p) (0 : Fin 1) rfl)

omit [W.IsMultiplicative] in
lemma value_empty (X : C) : value L hL (emptyObj W X) = 𝟙 (L.obj X) := by
  unfold value
  simp only [emptyObj, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (path L hL (emptyObj W X)).map (𝟙 (0 : Fin 1)) = _
  exact (path L hL (emptyObj W X)).map_id _

lemma colimitValue_arrowPoint {X Y : C} (p : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (colimitValue L hL X Y).app n (arrowPoint W p n) = L.map p :=
  (colimitValue_inclusion_app L hL X Y (Word.single .forward) (arrowSimplex W p n)).trans
    (value_forward L hL p)

end SerrePositivity.EInfinity.Hammock.Zigzag.Value
