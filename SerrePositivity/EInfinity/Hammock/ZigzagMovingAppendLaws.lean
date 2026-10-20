module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixed

/-!
# 動く接合点での貼り合わせと恒等・合成

概要：全頂点での実際の貼り合わせは恒等縦射と合成を保持する。
方針：接合点の左と右で元の成分へ展開し、移送の同型を消す。
規約：共有端点は動いてよい。接合条件の証明の選択には依存しない。
使われ方：ブロック置換の関手性・比較自然変換の検証。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : Word} {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  {S : Zigzag W a X Y} {S' : Zigzag W a X' Y'} {S'' : Zigzag W a X'' Y''}
  {T : Zigzag W b Y Z} {T' : Zigzag W b Y' Z'} {T'' : Zigzag W b Y'' Z''}

lemma map_id (S : Zigzag W a X Y) (T : Zigzag W b Y Z)
    (hj : HEq ((Zigzag.MovingHom.id S).app (Fin.last a.length))
      ((Zigzag.MovingHom.id T).app 0)) :
    map (Zigzag.MovingHom.id S) (Zigzag.MovingHom.id T) hj =
      Zigzag.MovingHom.id (obj S T) := by
  apply Zigzag.MovingHom.ext
  intro k
  dsimp only [map, app, Zigzag.MovingHom.id]
  split_ifs <;> simp <;> rfl

lemma map_comp (f : Zigzag.MovingHom S S') (g : Zigzag.MovingHom T T')
    (f' : Zigzag.MovingHom S' S'') (g' : Zigzag.MovingHom T' T'')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hj' : HEq (f'.app (Fin.last a.length)) (g'.app 0))
    (hj'' : HEq ((f.comp f').app (Fin.last a.length)) ((g.comp g').app 0)) :
    (map f g hj).comp (map f' g' hj') = map (f.comp f') (g.comp g') hj'' := by
  apply Zigzag.MovingHom.ext
  intro k
  dsimp only [map, app, Zigzag.MovingHom.comp]
  split_ifs <;> simp

end SerrePositivity.EInfinity.Hammock.ZigzagAppend.Moving
