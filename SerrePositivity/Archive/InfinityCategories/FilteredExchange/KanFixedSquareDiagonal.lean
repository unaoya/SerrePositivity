module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleIsoFaces
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTriangleSquare

/-!
概要：指定した上下辺を持つ空間の正方形の元の対角を、同じ Kan 対象間で回収する。
方針：上下辺の端点から対角の両端だけを合わせ、辺と射の全単射を使う。
規約：対角を充填で選ばない。使われ方：同じ全正方形の上下二三角形の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : KanObject.{u}} (f g : X ⟶ Y)
  (Q : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ SpaceInfinity.{u})
  (hb : SSet.yonedaEquiv (SSet.ι₀ ≫ Q) = (coherentNerveEdge f).edge)
  (ht : SSet.yonedaEquiv (SSet.ι₁ ≫ Q) = (coherentNerveEdge g).edge)

/-- 元の正方形の対角の端点だけを、元の上下辺の両端へそろえる。 -/
def kanFixedSquareDiagonalEdge : SpaceInfinity.{u}.Edge
    (coherentNerveVertex X) (coherentNerveVertex Y) := by
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  let b := (homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u + 1}))
      (stdSimplex.obj₀Equiv.symm 0))).map ((truncation 2).map Q)
  let t := (homotopyIntervalEdge.tensor (SSet.Truncated.Edge.id
    (X := (truncation 2).obj (Δ[1] : SSet.{u + 1}))
      (stdSimplex.obj₀Equiv.symm 1))).map ((truncation 2).map Q)
  have hb' : b.edge = (coherentNerveEdge f).edge := by
    change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    exact hb
  have ht' : t.edge = (coherentNerveEdge g).edge := by
    change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    exact ht
  let d := (homotopyIntervalEdge.tensor homotopyIntervalEdge).map ((truncation 2).map Q)
  refine SSet.Edge.ofTruncated ⟨d.edge, d.src_eq.trans ?_, d.tgt_eq.trans ?_⟩
  · exact b.src_eq.symm.trans ((congrArg (SpaceInfinity.δ 1) hb').trans
      (coherentNerveEdge f).src_eq)
  · exact t.tgt_eq.symm.trans ((congrArg (SpaceInfinity.δ 0) ht').trans
      (coherentNerveEdge g).tgt_eq)

/-- 元の対角辺の Kan 値の射。 -/
def kanFixedSquareDiagonal : X ⟶ Y :=
  coherentNerveEdgeToHom (kanFixedSquareDiagonalEdge f g Q hb ht)

/-- Kan 値の対角の辺は、元の全正方形の対角そのもの。 -/
lemma kanFixedSquareDiagonal_edge :
    (coherentNerveEdge (kanFixedSquareDiagonal f g Q hb ht)).edge =
      SSet.yonedaEquiv (squareDiagonal ≫ Q) := by
  have he := congrArg SSet.Edge.edge
    (coherentNerveEdge_hom (kanFixedSquareDiagonalEdge f g Q hb ht))
  refine he.trans ?_
  change Q.app (Opposite.op ⦋1⦌) (homotopyIntervalEdge.edge, homotopyIntervalEdge.edge) = _
  rw [SSet.yonedaEquiv_comp]
  congr 1
  apply Prod.ext <;> decide

end SerrePositivity.InfinityCategories.F2
