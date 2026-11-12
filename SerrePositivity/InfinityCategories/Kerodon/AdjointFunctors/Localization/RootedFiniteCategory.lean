module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeEndpointHull
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverSubsetLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 元の両端を含む有限包の固定語の圏と包含

概要：各有限集合の根に閉じた包上の元の zigzag 圏を作る。
方針：元の部分集合の相対包含と元の端点の等式を使う。
規約：全端点は元の X,Y の同じ部分型表示を選ぶ。
使われ方：有限部分集合の strict hammock 図式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

abbrev hull (S : Finset Q) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull T X Y S

def left (S : Finset Q) : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (hull T X Y S)) :=
  show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (hull T X Y S) from
    ⟨X, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_left T X Y S⟩

def right (S : Finset Q) : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (hull T X Y S)) :=
  show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (hull T X Y S) from
    ⟨Y, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_right T X Y S⟩

def termCategory (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (S : Finset Q) : Cat.{max u v, max u v} := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (hull T X Y S)
  exact Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (hull T X Y S))))
    a (left T X Y S) (right T X Y S))

def mapFunctor (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) {S R : Finset Q} (h : S ⊆ R) :
    termCategory T X Y a S ⥤ termCategory T X Y a R := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (hull T X Y S)
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (hull T X Y R)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.subsetRelative (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.endpointHull_mono T X Y h)) rfl rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RootedFiniteCategory
