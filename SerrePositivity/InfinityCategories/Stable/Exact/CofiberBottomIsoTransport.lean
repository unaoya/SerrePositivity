module
public import SerrePositivity.InfinityCategories.F1B.SpecifiedHomotopyLift
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorChoice
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationStability
/-!
概要：cofiber 四角形の底辺の全関手同型を、cofiber 四角形全体の実同型へ延長する。
方針：指定底辺の可逆ホモトピーを単射に沿って延長し、同じ底辺の cofiber 比較を使う。
規約：零頂点と実押し出し性を保持。使われ方：Verdier 分数表示による完全性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 底辺が全関手圏で同型な二つの実 cofiber 四角形は、四角形全体として同型。 -/
lemma nonempty_cofiberSquareFunctorIso_of_bottom_iso {X : SSet.{u}} [Quasicategory X]
    (s t : ZeroTriangle X) (hs : IsCofiberSequence s) (ht : IsCofiberSequence t)
    (e : FunctorIso (squareBottomEdge ≫ s.square) (squareBottomEdge ≫ t.square)) :
    Nonempty (FunctorIso s.square t.square) := by
  let H := FunctorIso.simplicialHomotopy e.symm
  have hH : ∀ a, IsInvertibleEdge (simplicialHomotopyVertexEdge H a).toTruncated := by
    intro a
    exact simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (FunctorIso.edge e.symm) (FunctorIso.edge_isInvertible e.symm) a
  obtain ⟨w, G, hw, _, hG⟩ := F2.exists_mono_homotopy_lift_target squareBottomEdge
    (squareBottomEdge ≫ t.square) s.square H hH
  let ew : FunctorIso w s.square := functorIsoOfPointwiseInvertibleHomotopy G hG
  let corner := squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 1
  have ez : VertexIso (squareVertex w 0 1) (squareVertex s.square 0 1) := by
    have h := VertexIso.map ew (evaluateFunctorAt (Y := X) corner)
    rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex] at h
    exact h
  let d : ZeroTriangle X := {
    square := w
    zero_corner := s.zero_corner.of_vertexIso ez.symm }
  have hd : IsCofiberSequence d := hs.of_functorIso ew.symm
  let f := edgeOfSimplex (SSet.yonedaEquiv (squareBottomEdge ≫ t.square))
  let r : CofiberSquare f := {
    toZeroTriangle := d
    bottom_edge := hw.trans (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := hd }
  let v : CofiberSquare f := {
    toZeroTriangle := t
    bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  obtain ⟨ev⟩ := nonempty_cofiberSquareFunctorIso r v
  exact ⟨ew.symm ≪≫ ev⟩
end SerrePositivity.InfinityCategories
