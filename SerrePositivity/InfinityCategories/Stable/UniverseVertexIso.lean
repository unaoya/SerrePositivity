module
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.Stable.UniverseSquareHom

/-! # 実頂点同型の宇宙持ち上げと降下

概要：ULift の頂点同型は、元の quasicategory の頂点同型へ戻せる。
方針：同型を実可逆辺で表示し、両側逆の合成二単体を各次数で降ろす。
規約：ホモトピー圏を定義的に同一視しない。使われ方：実安定閉包の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}}

/-- 持ち上げた quasicategory の実辺を元の宇宙へ降ろす。 -/
def downTruncatedEdge {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y) :
    Truncated.Edge (X := (truncation 2).obj X) x.down y.down where
  edge := e.edge.down
  src_eq := congrArg ULift.down e.src_eq
  tgt_eq := congrArg ULift.down e.tgt_eq

/-- 合成二単体も元の三辺を保持して降下する。 -/
def downTruncatedCompStruct {x y z : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y}
    {f : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) y z}
    {g : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x z}
    (c : Truncated.Edge.CompStruct e f g) :
    Truncated.Edge.CompStruct (downTruncatedEdge e) (downTruncatedEdge f)
      (downTruncatedEdge g) where
  simplex := c.simplex.down
  d₂ := congrArg ULift.down c.d₂
  d₀ := congrArg ULift.down c.d₀
  d₁ := congrArg ULift.down c.d₁

/-- 恒等辺の降下は元の頂点の恒等辺。 -/
lemma downTruncatedEdge_id (x : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌) :
    downTruncatedEdge (Truncated.Edge.id x) =
      Truncated.Edge.id (X := (truncation 2).obj X) x.down := rfl

/-- 実可逆辺の両側逆も元の宇宙へ降下する。 -/
lemma IsInvertibleEdge.down [Quasicategory X]
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌}
    {e : Truncated.Edge (X := (truncation 2).obj ((SSet.uliftFunctor.{v, u}).obj X)) x y}
    (he : IsInvertibleEdge e) : IsInvertibleEdge (downTruncatedEdge e) := by
  obtain ⟨g, t₁, t₂⟩ := he.nonempty_inverse
  refine ⟨⟨Truncated.HomotopyCategory.homMk (downTruncatedEdge g), ?_, ?_⟩⟩
  · simpa only [downTruncatedEdge_id, Truncated.HomotopyCategory.homMk_id] using
      Truncated.HomotopyCategory.homMk_comp_homMk (downTruncatedCompStruct t₁)
  · simpa only [downTruncatedEdge_id, Truncated.HomotopyCategory.homMk_id] using
      Truncated.HomotopyCategory.homMk_comp_homMk (downTruncatedCompStruct t₂)

/-- 元の実頂点同型を持ち上げる。 -/
def uliftVertexIso [Quasicategory X] {x y : X _⦋0⦌} (e : VertexIso x y) :
    VertexIso (X := (SSet.uliftFunctor.{v, u}).obj X) (ULift.up x) (ULift.up y) := by
  let a := Classical.choose (homotopyCategory_homMk_surjective x y e.hom)
  have ha := Classical.choose_spec (homotopyCategory_homMk_surjective x y e.hom)
  have hi : IsInvertibleEdge a := by rw [IsInvertibleEdge, ha]; infer_instance
  let := IsInvertibleEdge.ulift.{u, v} hi
  exact asIso (Truncated.HomotopyCategory.homMk (uliftTruncatedEdge.{u, v} a))

/-- 持ち上げた実頂点の同型を元の宇宙へ降ろす。 -/
def downVertexIso [Quasicategory X]
    {x y : ((SSet.uliftFunctor.{v, u}).obj X) _⦋0⦌} (e : VertexIso x y) :
    VertexIso (X := X) x.down y.down := by
  let a := Classical.choose (homotopyCategory_homMk_surjective x y e.hom)
  have ha := Classical.choose_spec (homotopyCategory_homMk_surjective x y e.hom)
  have hi : IsInvertibleEdge a := by rw [IsInvertibleEdge, ha]; infer_instance
  let := hi.down
  exact asIso (Truncated.HomotopyCategory.homMk (downTruncatedEdge a))

end SerrePositivity.InfinityCategories
