module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordIdentity

/-!
# 語の等式に沿う元の zigzag の比較

概要：同じ番号の全頂点・全列・全縦射を比較して、語の等式に沿う異種等式を得る。
方針：語の等式を消去し、構成済みの対象・縦射の外延性を使う。
規約：語の遷移は元の WordAction を使い、別の圧縮関手へ置き換えない。
使われ方：語の連結の単位・結合を実際の graph の等式へ移す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b : Word} {X Y : C}

lemma Zigzag.object_word_hext (h : a = b) (S : Zigzag W a X Y) (T : Zigzag W b X Y)
    (hv : ∀ i j, i.val = j.val → S.vertex i = T.vertex j)
    (ha : ∀ i j, i.val = j.val → HEq (S.arrow i) (T.arrow j)) : HEq S T := by
  cases h
  exact heq_of_eq (Zigzag.object_ext S T (fun i => hv i i rfl) (fun i => ha i i rfl))

lemma Zigzag.hom_word_hext (h : a = b)
    {S T : Zigzag W a X Y} {S' T' : Zigzag W b X Y}
    (hS : HEq S S') (hT : HEq T T') (f : Zigzag.Hom S T) (g : Zigzag.Hom S' T')
    (ha : ∀ i j, i.val = j.val → HEq (f.app i) (g.app j)) : HEq f g := by
  cases h
  exact Zigzag.hom_hext (eq_of_heq hS) (eq_of_heq hT) f g (fun i => ha i i rfl)

/-- 元の語の等式による遷移は、同じ元の対象を回収する。 -/
lemma WordAction.obj_eqToHom_heq [W.IsMultiplicative] (h : a = b) (S : Zigzag W a X Y) :
    HEq (WordAction.obj (eqToHom h) S) S := by
  cases h
  exact heq_of_eq (WordAction.obj_id S)

/-- 元の語の等式による遷移は、同じ元の全縦射を回収する。 -/
lemma WordAction.map_eqToHom_heq [W.IsMultiplicative] (h : a = b)
    {S T : Zigzag W a X Y} (f : S ⟶ T) : HEq (WordAction.map (eqToHom h) f) f := by
  cases h
  apply Zigzag.hom_hext (WordAction.obj_id S) (WordAction.obj_id T)
  intro i
  exact Zigzag.app_heq f (Word.Hom.cut_id a i)

end SerrePositivity.EInfinity.Hammock
