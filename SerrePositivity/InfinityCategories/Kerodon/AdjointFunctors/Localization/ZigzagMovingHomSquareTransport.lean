module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom

/-!
# 動く端点の全縦射の列の移送

概要：局所端点が動く場合にも、元の列の正方形を位置の等式に沿って移す。
方針：両端の位置の等式を消去し、元の MovingHom.comm に戻す。
規約：端点の縦射を恒等射とは仮定しない。
使われ方：局所ブロックの射列と各列の自然変換の抽出。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y'}

lemma square_transport (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (i : Fin w.length)
    (l r : Fin (w.length + 1)) (hl : l = w.source i) (hr : w.target i = r) :
    (eqToHom (congrArg S.vertex hl) ≫ S.arrow i ≫ eqToHom (congrArg S.vertex hr)) ≫
        f.app r =
      f.app l ≫ eqToHom (congrArg T.vertex hl) ≫ T.arrow i ≫
        eqToHom (congrArg T.vertex hr) := by
  subst l
  subst r
  simpa using f.comm i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport (square_transport)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport
