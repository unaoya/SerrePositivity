module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagPathSupport
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverArrowLift
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverPathRelative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeZigzagFunctor

/-!
# 有限支持に持ち上げた元の hammock grid の各行

概要：元の全横射列の生成辺を保って有限頂点側の行を構成する。
方針：元の支持の所属証明と一意な射列の持ち上げを使う。
規約：元の両端の頂点と first・last を保持する。
使われ方：元の全 grid の関手的な持ち上げ。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteGrid
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)] {a : Word} {X Y : Paths Q}
  (S : Finset Q) (F : I ⥤ Zigzag (⊤ : MorphismProperty (Paths Q)) a X Y)
  (hx : (show Q from X) ∈ S) (hy : (show Q from Y) ∈ S) (hF : gridPathSupport F ⊆ S)

def vertex (i : I) (j : Fin (a.length + 1)) : FiniteQuiver.Vertex S :=
  ⟨(F.obj i).vertex j, hF (gridPathSupport_vertex F i j)⟩

def row (i : I) : letI := FiniteQuiver.quiver S
    Zigzag (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) a
      ((Paths.of (FiniteQuiver.Vertex S)).obj ⟨X, hx⟩)
      ((Paths.of (FiniteQuiver.Vertex S)).obj ⟨Y, hy⟩) := by
  letI := FiniteQuiver.quiver S
  exact
    { vertex j := (Paths.of (FiniteQuiver.Vertex S)).obj (vertex S F hF i j)
      first := congrArg (Paths.of (FiniteQuiver.Vertex S)).obj (Subtype.ext (F.obj i).first)
      last := congrArg (Paths.of (FiniteQuiver.Vertex S)).obj (Subtype.ext (F.obj i).last)
      arrow k := FiniteQuiver.liftArrow S (vertex S F hF i (a.source k))
        (vertex S F hF i (a.target k)) ((F.obj i).arrow k)
          (fun _ hp => hF (gridPathSupport_horizontal F i k hp))
      backward_mem _ _ := trivial }

lemma row_projection (i : I) : letI := FiniteQuiver.quiver S
    Zigzag.Relative.obj (FiniteQuiver.pathRelative S) (row S F hx hy hF i) = F.obj i := by
  let := FiniteQuiver.quiver S
  apply Zigzag.object_ext
  · intro j; rfl
  · intro k
    exact heq_of_eq (FiniteQuiver.liftArrow_projection S (vertex S F hF i (a.source k))
      (vertex S F hF i (a.target k)) ((F.obj i).arrow k) _)

lemma row_arrow_projection (i : I) (k : Fin a.length) : letI := FiniteQuiver.quiver S
    (FiniteQuiver.pathInclusion S).map ((row S F hx hy hF i).arrow k) = (F.obj i).arrow k := by
  let := FiniteQuiver.quiver S
  exact FiniteQuiver.liftArrow_projection S (vertex S F hF i (a.source k))
    (vertex S F hF i (a.target k)) ((F.obj i).arrow k) _

end SerrePositivity.EInfinity.Hammock.FiniteGrid
