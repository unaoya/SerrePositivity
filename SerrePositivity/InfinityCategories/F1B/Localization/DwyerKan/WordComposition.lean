module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordSegmentComparison

/-!
# 語の合成と元の遷移関手の合成

概要：二つの語の写像に沿う二度の圧縮は、合成語に沿う一度の圧縮と一致する。
方針：切断の合成則と圧縮後の区間合成の回収を、全列と全縦射で使う。
規約：元の関手の厳密な等式。自然同型だけで置き換えない。
使われ方：全語の graph 図式の合成則。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b c : Word} {X Y : C}
  [W.IsMultiplicative]

/-- 二度の列の圧縮と、合成写像による元の列の圧縮の異種等式。 -/
lemma column_comp_heq (f : a ⟶ b) (g : b ⟶ c) (S : Zigzag W a X Y) (j : Fin c.length) :
    HEq (column (f ≫ g) S j) (column g (obj f S) j) := by
  let V := fun k => S.vertex ((f ≫ g).cut k)
  let U := fun k => S.vertex (f.cut (g.cut k))
  have hV : V = U := funext (fun k => congrArg S.vertex (Word.Hom.cut_comp f g k))
  let hd := fun i hi hi' => g.fiber_direction j i hi hi'
  have h := segment_heq_of_eq (c.direction j) S
    (Word.Hom.cut_comp f g j.castSucc) (Word.Hom.cut_comp f g j.succ)
    ((f ≫ g).cut_monotone (Fin.castSucc_le_succ j))
    (f.cut_monotone (g.cut_monotone (Fin.castSucc_le_succ j)))
    (fun i hi hi' => (f ≫ g).fiber_direction j i hi hi')
    (interval_direction f (c.direction j) (g.cut j.castSucc) (g.cut j.succ) hd)
  have hm := h.trans (heq_of_eq (segment_obj f (c.direction j) S
    (g.cut j.castSucc) (g.cut j.succ) (g.cut_monotone (Fin.castSucc_le_succ j)) hd).symm)
  exact columnAux_heq V U hV _ _ _ _ _ hm

/-- 二度の圧縮の元の全頂点・全列は、合成写像によるものと一致。 -/
lemma obj_comp (f : a ⟶ b) (g : b ⟶ c) (S : Zigzag W a X Y) :
    obj (f ≫ g) S = obj g (obj f S) :=
  Zigzag.object_ext _ _ (fun j => congrArg S.vertex (Word.Hom.cut_comp f g j))
    (column_comp_heq f g S)

/-- 語の写像の合成は、同じ元の遷移関手の合成に厳密に一致する。 -/
lemma functor_comp (f : a ⟶ b) (g : b ⟶ c) :
    functor (W := W) (X := X) (Y := Y) (f ≫ g) = functor f ⋙ functor g := by
  apply Functor.hext (fun S => obj_comp f g S)
  intro S T η
  apply Zigzag.hom_hext (obj_comp f g S) (obj_comp f g T)
  intro j
  exact Zigzag.app_heq η (Word.Hom.cut_comp f g j)

end SerrePositivity.EInfinity.Hammock.WordAction
