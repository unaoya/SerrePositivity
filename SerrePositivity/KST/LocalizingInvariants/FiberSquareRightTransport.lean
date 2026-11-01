module

public import SerrePositivity.KST.LocalizingInvariants.FiberSquareComparison
public import SerrePositivity.InfinityCategories.F1B.SpecifiedFunctorEdgeLift
public import SerrePositivity.InfinityCategories.Stable.SquareFunctorTransport
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Stable.SuspensionSquare

/-!
概要：fiber 四角形の右辺の指定関手同型を、全四角形の可逆辺へ厳密に持ち上げる。
方針：右辺包含の単射性と指定辺の相対持ち上げで、引き戻し性と零角を輸送する。
規約：右辺の元の一単体を保持。使われ方：d8 の中項を実積とする fiber 四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma fiberSquare_source_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : FiberSquare f) :
    squareVertex s.square 1 0 = x := by
  have h := squareRightEdge_source s.square
  rw [s.right_edge] at h
  exact h.symm.trans
    ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.src_eq)

lemma fiberSquare_target_vertex {X : SSet.{u}} {x y : X _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj X) x y} (s : FiberSquare f) :
    squareVertex s.square 1 1 = y := by
  have h := squareRightEdge_target s.square
  rw [s.right_edge] at h
  exact h.symm.trans
    ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply f.edge)).trans f.tgt_eq)

lemma exists_fiberSquare_right_transport {X : SSet.{u}} [Quasicategory X]
    (t : ZeroTriangle X) (ht : IsFiberSequence t) (g : (Δ[1] : SSet.{u}) ⟶ X)
    (e : FunctorIso g (squareRightEdge ≫ t.square)) :
    ∃ s : FiberSquare (edgeOfSimplex (SSet.yonedaEquiv g)),
      ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X))
        (functorVertex s.square) (functorVertex t.square),
        IsInvertibleEdge l ∧
          ((pre squareRightEdge).app X).app (Opposite.op ⦋1⦌) l.edge = e.edge.edge := by
  have : Mono squareRightEdge.{u} := by
    have h : squareRightEdge.{u} ≫ snd (Δ[1] : SSet.{u}) Δ[1] = 𝟙 Δ[1] := rfl
    exact mono_of_mono_fac h
  obtain ⟨G, hG, l, hl, hi⟩ := F2.exists_precomposition_edge_lift
    squareRightEdge g t.square e.edge e.edge_isInvertible
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk l) := hi
  let d : FunctorIso G t.square := asIso (SSet.Truncated.HomotopyCategory.homMk l)
  have hz : IsZeroVertex (squareVertex G 0 1) := by
    let v : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌ :=
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    have he : VertexIso (squareVertex G 0 1) (squareVertex t.square 0 1) := by
      have hv := VertexIso.map d (evaluateFunctorAt v)
      simp only [evaluateFunctorAt_functorVertex] at hv
      change VertexIso (squareVertex G 0 1) (squareVertex t.square 0 1) at hv
      exact hv
    exact t.zero_corner.of_vertexIso he.symm
  let s : FiberSquare (edgeOfSimplex (SSet.yonedaEquiv g)) := {
    square := G
    zero_corner := hz
    right_edge := hG.trans (SSet.yonedaEquiv.symm_apply_apply g).symm
    isPullback := IsPullbackSquare.of_functorIso ht d.symm }
  exact ⟨s, l, hi, hl⟩

end SerrePositivity.KST.LocalizingInvariants
