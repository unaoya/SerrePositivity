module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathSupport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverArrowLift
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiverPathRelative
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor

/-!
# 有限支持に持ち上げた元の hammock grid の各行

概要：元の全横射列の生成辺を保って有限頂点側の行を構成する。
方針：元の支持の所属証明と一意な射列の持ち上げを使う。
規約：元の両端の頂点と first・last を保持する。
使われ方：元の全 grid の関手的な持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths Q}
  (S : Finset Q) (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)
  (hx : (show Q from X) ∈ S) (hy : (show Q from Y) ∈ S) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport F ⊆ S)

def vertex (i : I) (j : Fin (a.length + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S :=
  ⟨(F.obj i).vertex j, hF (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport_vertex F i j)⟩

def row (i : I) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S))) a
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj ⟨X, hx⟩)
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj ⟨Y, hy⟩) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact
    { vertex j := (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (vertex S F hF i j)
      first := congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext (F.obj i).first)
      last := congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)).obj (Subtype.ext (F.obj i).last)
      arrow k := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow S (vertex S F hF i (a.source k))
        (vertex S F hF i (a.target k)) ((F.obj i).arrow k)
          (fun _ hp => hF (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.gridPathSupport_horizontal F i k hp))
      backward_mem _ _ := trivial }

lemma row_projection (i : I) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathRelative S) (row S F hx hy hF i) = F.obj i := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j; rfl
  · intro k
    exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow_projection S (vertex S F hF i (a.source k))
      (vertex S F hF i (a.target k)) ((F.obj i).arrow k) _)

lemma row_arrow_projection (i : I) (k : Fin a.length) : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).map ((row S F hx hy hF i).arrow k) = (F.obj i).arrow k := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftArrow_projection S (vertex S F hF i (a.source k))
    (vertex S F hF i (a.target k)) ((F.obj i).arrow k) _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteGridRows
