module
public import SerrePositivity.InfinityCategories.Stable.ZeroOuterSpans
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSourceInitial
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullSubcomplexEquivalenceLifting

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroOuterSpanVertex_square_iff {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    IsZeroOuterSpanVertex
      (((pre spanSquareBoundary).app X).app (Opposite.op ⦋0⦌) v) ↔
      IsZeroCornerSquareVertex v := by
  have hF : functorVertex (squareDiagram v) = v :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [← hF]
  change IsZeroTargetArrow (functorVertex
    (horn₂₀.ι₀₁ ≫ spanSquareBoundary ≫ squareDiagram v)) ∧
    IsZeroTargetArrow (functorVertex
      (horn₂₀.ι₀₂ ≫ spanSquareBoundary ≫ squareDiagram v)) ↔ _
  rw [← Category.assoc, spanSquareBoundary_bottomEdge,
    ← Category.assoc, spanSquareBoundary_leftEdge]
  unfold IsZeroTargetArrow
  rw [evaluateFunctorAt_functorVertex, evaluateFunctorAt_functorVertex]
  rfl

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroCornerSquareSpan (X : SSet.{u}) : zeroCornerSquares X ⟶ zeroOuterSpans X :=
  fullSubcomplexLift IsZeroOuterSpanVertex
    ((fullSubcomplexOnVertices _ IsZeroCornerSquareVertex).ι ≫ (pre spanSquareBoundary).app X)
    (fun v ↦ (zeroOuterSpanVertex_square_iff v.val).mpr
      (fullSubcomplexOnVertices_vertex v))

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma squareDiagram_vertex_evaluation {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) (i j : Fin 2) :
    (evaluateFunctorAt (Y := X)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)).app (Opposite.op ⦋0⦌) v =
      squareVertex (squareDiagram v) i j := by
  have hF : functorVertex (squareDiagram v) = v :=
    (functorVertexEquiv _ _).apply_symm_apply v
  have h := evaluateFunctorAt_functorVertex
    (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j) (squareDiagram v)
  rw [hF] at h
  exact h

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma isZeroCornerSquareVertex_iff_of_vertexIso {X : SSet.{u}} [Quasicategory X]
    {a b : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌} (e : VertexIso a b) :
    IsZeroCornerSquareVertex a ↔ IsZeroCornerSquareVertex b := by
  have he (i j : Fin 2) : VertexIso (squareVertex (squareDiagram a) i j)
      (squareVertex (squareDiagram b) i j) := by
    have h := e.map (evaluateFunctorAt (Y := X)
      (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
    simpa only [squareDiagram_vertex_evaluation] using h
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.of_vertexIso (he 1 0), h₂.of_vertexIso (he 0 1)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁.of_vertexIso (he 1 0).symm, h₂.of_vertexIso (he 0 1).symm⟩

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpan_kanEquivalenceLifting (X : SSet.{u}) [Quasicategory X] :
    SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (zeroCornerSquareSpan X) := by
  have : Mono spanSquareBoundary.{u} := by
    dsimp only [spanSquareBoundary]
    infer_instance
  intro A B i hi he
  exact kanEquivalenceLifting_fullRestriction IsZeroCornerSquareVertex
    (fun e ↦ isZeroCornerSquareVertex_iff_of_vertexIso e) IsZeroOuterSpanVertex
    (zeroCornerSquareSpan X) ((pre spanSquareBoundary).app X) rfl
    (SerrePositivity.InfinityCategories.F1B.equivalenceLifting_pre spanSquareBoundary) i hi he
end SerrePositivity.InfinityCategories
