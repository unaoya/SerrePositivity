module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 動く接合点での貼り合わせと恒等・合成

概要：全頂点での実際の貼り合わせは恒等縦射と合成を保持する。
方針：接合点の左と右で元の成分へ展開し、移送の同型を消す。
規約：共有端点は動いてよい。接合条件の証明の選択には依存しない。
使われ方：ブロック置換の関手性・比較自然変換の検証。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y Z X' Y' Z' X'' Y'' Z'' : C}
  {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} {S' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X' Y'} {S'' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X'' Y''}
  {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z} {T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y' Z'} {T'' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y'' Z''}

lemma map_id (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b Y Z)
    (hj : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id S).app (Fin.last a.length))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id T).app 0)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id T) hj =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj S T) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro k
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id]
  split_ifs <;> simp <;> rfl

lemma map_comp (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S S') (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T T')
    (f' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S' S'') (g' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom T' T'')
    (hj : HEq (f.app (Fin.last a.length)) (g.app 0))
    (hj' : HEq (f'.app (Fin.last a.length)) (g'.app 0))
    (hj'' : HEq ((f.comp f').app (Fin.last a.length)) ((g.comp g').app 0)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f g hj).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f' g' hj') = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (f.comp f') (g.comp g') hj'' := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
  intro k
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.comp]
  split_ifs <;> simp

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws
