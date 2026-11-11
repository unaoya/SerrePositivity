module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramAppend

/-!
# 端点関手の表示変更と元の全図式の連結

概要：共有端点を含む図式の異種等式を連結した全図式へ移す。
方針：元の端点関手と図式の等式で帰納する。
規約：元の全縦射と接合点の縦射を保持する。
使われ方：prefix・残りの再添字の全図式の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
noncomputable section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {A A' B B' E E' : D ⥤ C}

lemma append_heq_endpoints (hA : A = A') (hB : B = B') (hE : E = E')
    {F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A B} {F' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W a A' B'}
    {G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B E} {G' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W b B' E'}
    (hF : HEq F F') (hG : HEq G G') : HEq (F.append G) (F'.append G') := by
  cases hA
  cases hB
  cases hE
  cases hF
  cases hG
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (append_heq_endpoints)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
