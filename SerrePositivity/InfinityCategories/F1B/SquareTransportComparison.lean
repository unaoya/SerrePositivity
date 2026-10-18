module

public import SerrePositivity.InfinityCategories.F1B.SquareBoundary
public import SerrePositivity.InfinityCategories.F1B.ThreeEdgeSquarePath
public import SerrePositivity.InfinityCategories.F1B.FunctorDiagramPathUniqueness

/-!
概要：三角形の境界輸送から補完した正方形と元の正方形を全境界固定で比較する。
方針：三角形の path を畳み込みで正方形へ移し、始点と全境界 path を照合する。
規約：二辺は固定、対角の path は全体比較の右辺そのものと一致することを使う。
使われ方：B1 の順方向比較から復元した comma 正方形と元の図式を結ぶ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：同じ境界 path を持つ三角形輸送の正方形補完と元の正方形は境界固定で結べる。
方針：畳み込みで輸送を正方形に移し、三辺と右辺で全境界 path の一致を証明する。
規約：輸送の path の終点だけでなく、指定した対角 path 全体の一致を要求する。
使われ方：B1 の復元した正方形から元の正方形への相対ホモトピー。 -/
lemma ThreeEdgeSquareComparison.exists_homotopy_to_triangleTransport
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} {T : FunctorCompositionTriangle l r d₀}
    {Q : FunctorCompositionSquare l r d₁} (c : ThreeEdgeSquareComparison T Q)
    (E : (Δ[2] : SSet.{u}) ⟶ equivalencePath ((ihom A).obj X))
    (hstart : E ≫ equivalencePathEndpoint _ 0 = T.diagram)
    (h₀ : stdSimplex.δ (0 : Fin 3) ≫ E =
      stdSimplex.δ (0 : Fin 3) ≫ T.diagram ≫ equivalencePathRefl _)
    (h₂ : stdSimplex.δ (2 : Fin 3) ≫ E =
      stdSimplex.δ (2 : Fin 3) ≫ T.diagram ≫ equivalencePathRefl _)
    (h₁ : stdSimplex.δ (1 : Fin 3) ≫ E = prismEndpoint 1 (Δ[1] : SSet.{u}) ≫ c.path) :
    ∃ H : SSet.Homotopy Q.diagram (squareUpperFold ≫ E ≫ equivalencePathEndpoint _ 1),
      (squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst _ (Δ[1] : SSet.{u}) ≫ squareBoundary.ι ≫ Q.diagram := by
  let L := squareUpperFold ≫ E
  have h₃ : squareThreeEdges.ι ≫ L =
      squareThreeEdges.ι ≫ Q.diagram ≫ equivalencePathRefl _ := by
    apply squareThreeEdges_restriction_eq L (Q.diagram ≫ equivalencePathRefl _)
    · change SSet.ι₀ ≫ squareUpperFold ≫ E = SSet.ι₀ ≫ Q.diagram ≫ _
      rw [← Category.assoc, squareUpperFold_bottom]
      simp only [Category.assoc, h₂, reassoc_of% T.vertex_zero, reassoc_of% Q.bottom]
      rw [← Category.assoc, SSet.comp_const]
    · change prismEndpoint 0 Δ[1] ≫ squareUpperFold ≫ E = prismEndpoint 0 Δ[1] ≫ Q.diagram ≫ _
      rw [← Category.assoc, squareUpperFold_left, h₂]
      rw [reassoc_of% T.face_two, reassoc_of% Q.left]
    · change SSet.ι₁ ≫ squareUpperFold ≫ E = SSet.ι₁ ≫ Q.diagram ≫ _
      rw [← Category.assoc, squareUpperFold_top, h₀]
      rw [reassoc_of% T.face_zero, reassoc_of% Q.top]
  have hb : squareBoundary.ι ≫ c.path = squareBoundary.ι ≫ L := by
    apply squareBoundary_restriction_eq
    · exact c.path_restriction.trans (by simpa only [Category.assoc] using h₃.symm)
    · change prismEndpoint 1 Δ[1] ≫ c.path = prismEndpoint 1 Δ[1] ≫ squareUpperFold ≫ E
      rw [← Category.assoc, squareUpperFold_right]
      exact h₁.symm
  have hs : c.path ≫ equivalencePathEndpoint _ 0 = L ≫ equivalencePathEndpoint _ 0 := by
    rw [c.path_zero]
    change (functorSquareOfCompositionTriangle T).diagram = (squareUpperFold ≫ E) ≫ _
    rw [Category.assoc, hstart, functorSquareOfCompositionTriangle_eq_fold]
  obtain ⟨H, hH⟩ := exists_functorDiagramPath_endpointHomotopy squareBoundary.ι c.path L hb hs
  let H' : SSet.Homotopy Q.diagram (squareUpperFold ≫ E ≫ equivalencePathEndpoint _ 1) :=
    { h := H.h
      h₀ := H.h₀.trans c.path_one
      h₁ := H.h₁
      rel := H.rel }
  refine ⟨H', ?_⟩
  have hend : squareBoundary.ι ≫ L ≫ equivalencePathEndpoint _ 1 =
      squareBoundary.ι ≫ Q.diagram := by
    have h := congrArg (fun k ↦ k ≫ equivalencePathEndpoint _ 1) hb.symm
    simpa only [Category.assoc, c.path_one] using h
  change (squareBoundary.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [hH, hend]

end SerrePositivity.InfinityCategories
