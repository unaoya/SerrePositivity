module
public import SerrePositivity.InfinityCategories.Stable.Exact.FullStableClosure

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

namespace FullSubcomplex
variable {X : SSet.{u}} (P : X _⦋0⦌ → Prop)

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
