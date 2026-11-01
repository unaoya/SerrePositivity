module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardTripleCollapse
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendObjects

/-!
# 元の三つの一列の連結と三列 collapse

概要：元の三射から貼った三列の圧縮は、元の合成射の一列に一致する。
方針：各連結の同じ頂点・同じ列を回収し、元の三列圧縮定理を適用する。
規約：任意の射を使い、前向き射に指定性を仮定しない。
使われ方：列内部の自然な三射の因子化の回収。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardTriple
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {X Y Z V : C}
  (e : X ⟶ Y) (f : Y ⟶ Z) (g : Z ⟶ V)

def append : Zigzag W Word.ForwardTriple.word X V :=
  ZigzagAppend.obj (ZigzagAppend.obj (ForwardZigzag.obj e) (ForwardZigzag.obj f))
    (ForwardZigzag.obj g)

lemma composite_append : composite (append (W := W) e f g) = e ≫ f ≫ g := by
  let E := ForwardZigzag.obj (W := W) e
  let F := ForwardZigzag.obj (W := W) f
  let G := ForwardZigzag.obj (W := W) g
  have h0 : Direction.arrow .forward (append (W := W) e f g) (0 : Fin 3)
      (Word.ForwardTriple.direction 0) = e := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) e
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (ZigzagAppend.arrow_left_heq (ZigzagAppend.obj E F) G
      ((0 : Fin 1).castAdd 1)).trans (ZigzagAppend.arrow_left_heq E F (0 : Fin 1))
  have h1 : Direction.arrow .forward (append (W := W) e f g) (1 : Fin 3)
      (Word.ForwardTriple.direction 1) = f := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) f
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact (ZigzagAppend.arrow_left_heq (ZigzagAppend.obj E F) G
      ((0 : Fin 1).natAdd 1)).trans (ZigzagAppend.arrow_right_heq E F (0 : Fin 1))
  have h2 : Direction.arrow .forward (append (W := W) e f g) (2 : Fin 3)
      (Word.ForwardTriple.direction 2) = g := by
    apply eq_of_heq
    change HEq (eqToHom _ ≫ _ ≫ eqToHom _) g
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    exact ZigzagAppend.arrow_right_heq (ZigzagAppend.obj E F) G (0 : Fin 1)
  simp only [composite, h0, h1, h2, eqToHom_refl, Category.id_comp, Category.comp_id]


lemma collapse_append [W.IsMultiplicative] :
    WordAction.obj Word.ForwardTriple.collapse (append (W := W) e f g) =
      ForwardZigzag.obj (e ≫ f ≫ g) := by
  rw [obj_eq, composite_append]

end SerrePositivity.EInfinity.Hammock.ForwardTriple
