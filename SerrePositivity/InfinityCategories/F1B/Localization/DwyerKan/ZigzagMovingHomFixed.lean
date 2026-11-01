module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingAppendFixed
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendMorphisms

/-!
# 元の固定端点の縦射を動く比較として回収する

概要：元の固定射の端点は同じ恒等射と異種等しい。
方針：first・last の等式と元の移送式を使う。
規約：射と全縦成分を変更しない。
使われ方：固定関手の自然性を動く接合点で貼り合わせる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingHom
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}
  {a b : Word} {X Y Z : C}

lemma ofHom_first {S T : Zigzag W a X Y} (f : Zigzag.Hom S T) :
    HEq ((ofHom f).app 0) (𝟙 X) := by
  apply (conj_eqToHom_iff_heq _ _ S.first T.first).1
  change f.app 0 = _
  simpa only [Category.id_comp, eqToHom_trans] using f.first

lemma ofHom_last {S T : Zigzag W a X Y} (f : Zigzag.Hom S T) :
    HEq ((ofHom f).app (Fin.last a.length)) (𝟙 Y) := by
  apply (conj_eqToHom_iff_heq _ _ S.last T.last).1
  change f.app (Fin.last a.length) = _
  simpa only [Category.id_comp, eqToHom_trans] using f.last

lemma ofHom_append {S S' : Zigzag W a X Y} {T T' : Zigzag W b Y Z}
    (f : Zigzag.Hom S S') (g : Zigzag.Hom T T')
    (hj : HEq ((ofHom f).app (Fin.last a.length)) ((ofHom g).app 0)) :
    ofHom (ZigzagAppend.map f g) = ZigzagAppend.Moving.map (ofHom f) (ofHom g) hj := by
  apply ext
  intro j
  rfl

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingHom
