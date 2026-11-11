module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramExt

/-!
# 元の端点表示を含む zigzag と全図式の外延性

概要：端点の等式・全対象・全列・全縦成分から元の全図式を異種等式で同定する。
方針：端点表示で帰納し、元の外延性を使う。
規約：弱同値や局所化後の同型で置き換えない。
使われ方：語の作用による prefix・残りの全図式の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v uD vD
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X X' Y Y' : C}

lemma object_hext_endpoints (hX : X = X') (hY : Y = Y')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y')
    (hv : ∀ i, S.vertex i = T.vertex i) (ha : ∀ i, HEq (S.arrow i) (T.arrow i)) : HEq S T := by
  cases hX
  cases hY
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext S T hv ha)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (object_hext_endpoints)


namespace MovingDiagram
variable {D : Type uD} [Category.{vD} D] [W.IsMultiplicative] {A A' B B' : D ⥤ C}

lemma hext_endpoints (hA : A = A') (hB : B = B')
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B) (G : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A' B')
    (ho : ∀ d, HEq (F.obj d) (G.obj d))
    (hm : ∀ {d e : D} (f : d ⟶ e) i, HEq ((F.map f).app i) ((G.map f).app i)) : HEq F G := by
  cases hA
  cases hB
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ext F G (fun d => eq_of_heq (ho d)) hm)

end MovingDiagram
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
