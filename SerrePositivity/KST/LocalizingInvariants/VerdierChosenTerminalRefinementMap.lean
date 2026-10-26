module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexRefinementCocone

/-!
概要：既に選んだ同じ実 pullback 補完から、元の全前段への実分母辺を回収する。
方針：実左下頂点を前段図式に戻し、元の左辺と終端列の一次単体を保持する。
規約：別の pullback 補完や別の前段を選び直さない。
使われ方：両端円柱で選んだ一様前段を、元の商余錐の全比較へそのまま接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

def terminalRefinementSourceDiagram {X : SSet.{u}} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) : (Δ[n] : SSet.{u}) ⟶ X :=
  F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
    evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

lemma terminalRefinementSourceDiagram_vertex {X : SSet.{u}} {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    squareVertex (terminalRefinementSquare F) 0 0 =
      functorVertex (terminalRefinementSourceDiagram F) := by
  change (internalHomFlipHomEquiv Δ[n] (Δ[1] ⊗ Δ[1]) X
    (F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι)).app (Opposite.op ⦋0⦌)
      ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)), (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _
  rw [internalHomFlipHomEquiv_app_zero]
  rfl

/-- 同じ実補完から、同じ一様前段・実終端分母の一次単体を保つ全前段分母を回収する。 -/
lemma exists_verdierChosenTerminalRefinementMap
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj)
    (hF : F ≫ pullbackProjection B.obj = simplexTerminalCospanFamily D
      ((joinStdSimplexIso 0 0).inv ≫ d.val.val) (verdierDenominatorDiagram_target i _ d))
    (hlast : F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnVertex ((joinStdSimplexIso 0 0).inv ≫ d.val.val)) :
    ∃ t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex (terminalRefinementSourceDiagram F)) (functorVertex D),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      (evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n))).app
        (Opposite.op ⦋1⦌) t.edge =
        (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))) d.val).edge := by
  let s := (joinStdSimplexIso 0 0).inv ≫ d.val.val
  let Q := terminalRefinementSquare F
  have hOrig : squareVertex Q 0 1 = functorVertex D :=
    terminalRefinementSquare_original D s (verdierDenominatorDiagram_target i _ d) F hF
  let t := ((SSet.Edge.ofTruncated (squareLeftArrow Q)).ofEq
    (terminalRefinementSourceDiagram_vertex F) hOrig).toTruncated
  have hQ : IsPullbackSquare Q := terminalRefinementSquare_isPullback F
  have hW : (squareLeftArrow Q).edge ∈
      (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
    apply (relativeFirstRowSimplex_pullback_iff h n Q hQ).mpr
    rw [relativeFirstRowSimplex_mem_edge_iff h n]
    intro k
    rw [squareRightArrow_edge, ← SSet.yonedaEquiv_comp]
    have hr := terminalRefinementSquare_right_evaluate D s
      (verdierDenominatorDiagram_target i _ d) F hF k
    rw [hr]
    exact fullSubcomplexOnVertices_vertex d
  have hQlast : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram s := by
    dsimp only [Q]
    rw [terminalRefinementSquare_evaluate, hlast]
    exact Equiv.symm_apply_apply _ _
  refine ⟨t, hW, ?_⟩
  change (evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n))).app
    (Opposite.op ⦋1⦌) (squareLeftArrow Q).edge = _
  rw [squareLeftArrow_edge, ← SSet.yonedaEquiv_comp, Category.assoc, hQlast]
  change SSet.yonedaEquiv (squareLeftEdge ≫ squareColumnDiagram s) = _
  simp only [squareColumnDiagram, ← Category.assoc, squareLeftEdge, lift_snd,
    Category.id_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants
