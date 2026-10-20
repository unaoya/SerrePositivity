module

public import SerrePositivity.KST.LocalizingInvariants.FullSubcomplexSquares
public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.InitialTransport

/-!
概要：零対象・fiber・cofiber に閉じた頂点条件の全部分圏は安定。
方針：周囲の指定 fiber/cofiber の四頂点の条件を確認し、双カルテジアンな実四角形を戻す。
規約：部分圏の安定性を入力しない。使われ方：通常 pullback の安定性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 周囲の実零三角形の cofiber と fiber に閉じる条件。 -/
structure StableVertexCondition {X : SSet.{u}} (P : X _⦋0⦌ → Prop) : Prop where
  zero (x) : IsZeroVertex x → P x
  cofiber (t : ZeroTriangle X) : IsCofiberSequence t →
    P (squareVertex t.square 0 0) → P (squareVertex t.square 1 0) →
      P (squareVertex t.square 1 1)
  fiber (t : ZeroTriangle X) : IsFiberSequence t →
    P (squareVertex t.square 1 0) → P (squareVertex t.square 1 1) →
      P (squareVertex t.square 0 0)

namespace FullSubcomplex
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

/-- 頂点条件を部分複体の零単体にする。 -/
def vertex (x : X _⦋0⦌) (hx : P x) :
    (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌ :=
  ⟨x, by intro v; have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
         subst v; simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩

variable [Quasicategory X] [IsStable X] (hP : StableVertexCondition P)

/-- 部分圏は周囲の選んだ零対象を含む。 -/
def zeroVertex : ZeroVertex (fullSubcomplexOnVertices X P : SSet.{u}) where
  vertex := vertex P (chosenZeroVertex X).vertex (hP.zero _ (chosenZeroVertex X).isZero)
  isInitial := (reflects_zero P _ (chosenZeroVertex X).isZero).1
  isTerminal := (reflects_zero P _ (chosenZeroVertex X).isZero).2

include hP

lemma inclusion_preservesZero : PreservesZeroVertices (fullSubcomplexOnVertices X P).ι := by
  intro x hx
  let z := zeroVertex P hP
  let e := terminalVertexIso hx.2 z.isTerminal
  exact (chosenZeroVertex X).isZero.of_vertexIso
    (VertexIso.map e (fullSubcomplexOnVertices X P).ι).symm

variable {x y : (fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
  (f : Truncated.Edge (X := (truncation 2).obj
    (fullSubcomplexOnVertices X P : SSet.{u})) x y)

omit [Quasicategory X] [IsStable X] in
lemma cofiber_vertices
    (s : CofiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι))) :
    ∀ i j : Fin 2, P (squareVertex s.square i j) := by
  have hs : P (squareVertex s.square 0 0) := by
    rw [s.source_vertex]; exact fullSubcomplexOnVertices_vertex x
  have ht : P (squareVertex s.square 1 0) := by
    rw [s.target_vertex]; exact fullSubcomplexOnVertices_vertex y
  intro i j
  fin_cases i <;> fin_cases j
  · exact hs
  · exact hP.zero _ s.zero_corner
  · exact ht
  · exact hP.cofiber s.toZeroTriangle s.isPushout hs ht

omit [Quasicategory X] [IsStable X] in
lemma fiber_vertices
    (s : FiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι))) :
    ∀ i j : Fin 2, P (squareVertex s.square i j) := by
  let g := f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι)
  have hs : squareVertex s.square 1 0 = x.val :=
    (squareRightEdge_source s.square).symm.trans
      ((congrArg (fun r ↦ X.δ 1 (SSet.yonedaEquiv r)) s.right_edge).trans
        ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.src_eq))
  have ht : squareVertex s.square 1 1 = y.val :=
    (squareRightEdge_target s.square).symm.trans
      ((congrArg (fun r ↦ X.δ 0 (SSet.yonedaEquiv r)) s.right_edge).trans
        ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.tgt_eq))
  have hp : P (squareVertex s.square 1 0) := by
    rw [hs]; exact fullSubcomplexOnVertices_vertex x
  have hq : P (squareVertex s.square 1 1) := by
    rw [ht]; exact fullSubcomplexOnVertices_vertex y
  intro i j
  fin_cases i <;> fin_cases j
  · exact hP.fiber s.toZeroTriangle s.isPullback hp hq
  · exact hP.zero _ s.zero_corner
  · exact hp
  · exact hq

/-- 閉性から元の全部分複体の安定性を導く。 -/
theorem isStable : IsStable (fullSubcomplexOnVertices X P : SSet.{u}) := by
  have : HasZeroVertex (fullSubcomplexOnVertices X P : SSet.{u}) := ⟨⟨(zeroVertex P hP).vertex,
    (zeroVertex P hP).isZero⟩⟩
  apply isStable_of_bicartesian_choices
  · intro x y f
    let s := chosenFiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι))
    refine ⟨fiberLift P f s (fiber_vertices P hP f s), reflects_pushout P _ ?_⟩
    change IsPushoutSquare (squareLift P s.square (fiber_vertices P hP f s) ≫ _)
    rw [squareLift_ι]
    exact IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback
  · intro x y f
    let s := chosenCofiberSquare (f.map ((truncation 2).map (fullSubcomplexOnVertices X P).ι))
    refine ⟨cofiberLift P f s (cofiber_vertices P hP f s), reflects_pullback P _ ?_⟩
    change IsPullbackSquare (squareLift P s.square (cofiber_vertices P hP f s) ≫ _)
    rw [squareLift_ι]
    exact IsStable.pullback_of_pushout s.toZeroTriangle s.isPushout

end FullSubcomplex
end SerrePositivity.KST.LocalizingInvariants
