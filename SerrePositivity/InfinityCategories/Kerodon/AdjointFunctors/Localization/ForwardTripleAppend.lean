module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleCollapse
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects

/-!
# 元の三つの一列の連結と三列 collapse

概要：元の三射から貼った三列の圧縮は、元の合成射の一列に一致する。
方針：各連結の同じ頂点・同じ列を回収し、元の三列圧縮定理を適用する。
規約：任意の射を使い、前向き射に指定性を仮定しない。
使われ方：列内部の自然な三射の因子化の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleAppend
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y Z V : C}
  (e : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ V)

def append : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.word X V :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj e) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj g)

lemma composite_append : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleCollapse.composite (append (W := W) e f g) = e ≫ f ≫ g := by
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) e
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) g
  have h0 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward (append (W := W) e f g) (0 : Fin 3)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 0) = e := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) e
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj E F) G
      ((0 : Fin 1).castAdd 1)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq E F (0 : Fin 1))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward (append (W := W) e f g) (1 : Fin 3)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 1) = f := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) f
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj E F) G
      ((0 : Fin 1).natAdd 1)).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq E F (0 : Fin 1))
  have h2 : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward (append (W := W) e f g) (2 : Fin 3)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.direction 2) = g := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) g
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj E F) G (0 : Fin 1)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleCollapse.composite, h0, h1, h2, eqToHom_refl, Category.id_comp, Category.comp_id]


lemma collapse_append [W.IsMultiplicative] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordForwardTripleCollapse.collapse (append (W := W) e f g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (e ≫ f ≫ g) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleCollapse.obj_eq, composite_append]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardTripleAppend
