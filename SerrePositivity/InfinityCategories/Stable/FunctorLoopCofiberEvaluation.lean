module
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceSpanColimits
public import SerrePositivity.InfinityCategories.Stable.FunctorLoopEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.Core.CocartesianPathSpace

/-!
概要：全関手圏の零角と cofiber 四角形を各点で評価する。
方針：零関手との自然同型と、各評価 span の余極限の存在を使う。
規約：元の圏の有限余極限や一般安定性を仮定しない。
使われ方：関手区間で構成する回転の両端の実 cofiber 列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：零である関手頂点の各評価も零である。
方針：定値零関手との自然同型を点で評価する。
規約：元の関手を定値と仮定しない。
使われ方：関手圏の cofiber の零角の評価。 -/
lemma IsZeroVertex.functor_evaluation {K X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] {v : ((ihom K).obj X) _⦋0⦌} (hv : IsZeroVertex v)
    (k : K _⦋0⦌) :
    IsZeroVertex ((evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌) v) := by
  let z := chosenZeroVertex X
  let w := functorVertex (SSet.const z.vertex : K ⟶ X)
  have hw : IsZeroVertex w := by
    apply isZeroVertex_functorVertex_of_pointwise
    intro a
    change IsZeroVertex (PinchedHom.constant z.vertex 0)
    rw [pinchedConstant_zero]
    exact z.isZero
  let e : VertexIso w v := hw.2.isTerminalHo.uniqueUpToIso hv.2.isTerminalHo
  have he := e.map (evaluateFunctorAt (Y := X) k)
  apply IsZeroVertex.of_vertexIso _ he
  change IsZeroVertex ((evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋0⦌)
    (functorVertex (SSet.const z.vertex : K ⟶ X)))
  rw [evaluateFunctorAt_functorVertex]
  change IsZeroVertex (PinchedHom.constant z.vertex 0)
  rw [pinchedConstant_zero]
  exact z.isZero

/-- 概要：零である区間関手の同じ区間辺は可逆である。
方針：両評価が零であることから、その間の辺の類を同型と判定する。
規約：元の区間辺を選び直さない。
使われ方：cofiber の零角の比較の可逆性。 -/
lemma IsZeroVertex.isEquivalencePathVertex {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X] {v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌}
    (hv : IsZeroVertex v) : IsEquivalencePathVertex v := by
  let e := intervalFunctorVertexTypedEdge v
  have h₀ := hv.functor_evaluation (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  have h₁ := hv.functor_evaluation (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have hi : IsInvertibleEdge e := isIso_of_isTerminal h₀.2.isTerminalHo h₁.2.isTerminalHo _
  exact (isInvertibleEdge_congr
    (show e.edge = (edgeOfSimplex (intervalFunctorVertexEdge v)).edge from rfl)).mp hi

/-- 概要：関手圏の cofiber 四角形の全評価は実 cofiber 四角形である。
方針：評価 span の零枝から余極限の存在を得て、全関手圏の余極限を評価する。
規約：有限余極限を追加仮定にしない。
使われ方：全図式族の回転の自然な両端。 -/
lemma ZeroTriangle.isCofiber_evaluate_of_loopEquivalence {K X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle ((ihom K).obj X)) (ht : IsCofiberSequence t) (k : K _⦋0⦌) :
    IsPushoutSquare (t.square ≫ evaluateFunctorAt k) := by
  apply (F2.isColimitCone_post_pushoutCocone_iff _ t.square).mp
  apply HomotopyLimits.isColimitCone_functor_evaluation_of_pointwise_exists
    (pushoutCocone t.square) ht _ k
  intro a
  change HasColimit (pushoutSpan t.square ≫ evaluateFunctorAt a)
  apply hasColimit_span_of_terminal_second_of_loopEquivalence s hs hΩ
  simp only [pushoutSpan, ← Category.assoc, spanSquareBoundary_leftEdge]
  change IsTerminalVertex ((evaluateFunctorAt (Y := X) a).app (Opposite.op ⦋0⦌)
    (squareVertex t.square 0 1))
  exact (t.zero_corner.functor_evaluation a).2

end SerrePositivity.InfinityCategories
