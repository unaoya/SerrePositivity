module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointTarget
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagramFibers

/-!
概要：cofiber の実右随伴の矢印は始点が零で、終点は元の入力である。
方針：恒等矢印の右辺を持つ元の cofiber 四角形を fiber として読む。
規約：同じ右辺切断と同じ関手を保持。使われ方：Cone の右随伴の零始点表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

/-- 恒等矢印を右辺として持つ、元の逆回転で選んだ cofiber 四角形。 -/
def cofiberRightAdjointDiagram (x : X _⦋0⦌) : (CofiberDiagrams.space X) _⦋0⦌ :=
  (CofiberRotation.rightSection X).app (Opposite.op ⦋0⦌)
    ((ArrowTarget.identityArrow X).app (Opposite.op ⦋0⦌) x)

lemma cofiberRightAdjointDiagram_right (x : X _⦋0⦌) :
    squareRightEdge ≫ squareDiagram (cofiberRightAdjointDiagram X x).val = SSet.const x := by
  apply functorVertex_injective
  rw [← _root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiber_diagram_right_vertex]
  have h := congrArg (fun f : (ihom (Δ[1] : SSet.{u})).obj X ⟶ _ =>
    f.app (Opposite.op ⦋0⦌) ((ArrowTarget.identityArrow X).app (Opposite.op ⦋0⦌) x))
    (CofiberRotation.rightSection_right X)
  change (CofiberDiagrams.right X).app (Opposite.op ⦋0⦌)
    (cofiberRightAdjointDiagram X x) = (ArrowTarget.identityArrow X).app (Opposite.op ⦋0⦌) x at h
  exact h.trans (constantFunctorMap_vertex Δ[1] x)

lemma cofiberRightAdjointDiagram_right_invertible (x : X _⦋0⦌) :
    IsInvertibleEdge (squareRightArrow (squareDiagram (cofiberRightAdjointDiagram X x).val)) := by
  let e := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have hi : IsInvertibleEdge e := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  apply (isInvertibleEdge_congr (e := e)
    (f := squareRightArrow (squareDiagram (cofiberRightAdjointDiagram X x).val)) ?_).1 hi
  rw [squareRightArrow_edge, cofiberRightAdjointDiagram_right]
  have hc : SSet.yonedaEquiv (SSet.const x : (Δ[1] : SSet.{u}) ⟶ X) =
      PinchedHom.constant x 1 := rfl
  exact (pinchedConstant_one x).symm.trans hc.symm

/-- 元の cofiber の右随伴は各入力を零始点の矢印へ送る。 -/
lemma cofiberRightAdjoint_source_zero (x : X _⦋0⦌) :
    IsZeroVertex ((cofiberRightAdjoint X ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex ((CofiberDiagrams.bottom X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app (Opposite.op ⦋0⦌)
      (cofiberRightAdjointDiagram X x))
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiber_diagram_bottom_source]
  exact CofiberDiagrams.zero_source_of_right_invertible X (cofiberRightAdjointDiagram X x)
    (cofiberRightAdjointDiagram_right_invertible X x)

end SerrePositivity.KST.LocalizingInvariants
