module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullStableClosure

public import SerrePositivity.KST.LocalizingInvariants.FullSubcomplexSquares
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

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

variable [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.StableVertexCondition P)

/-- 部分圏は周囲の選んだ零対象を含む。 -/
def zeroVertex : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) where
  vertex := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.vertex P (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).vertex (hP.zero _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isZero)
  isInitial := (reflects_zero P _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isZero).1
  isTerminal := (reflects_zero P _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isZero).2

include hP

lemma inclusion_preservesZero : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι := by
  intro x hx
  let z := zeroVertex P hP
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.terminalVertexIso hx.2 z.isTerminal
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex X).isZero.of_vertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).symm

variable {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) _⦋0⦌}
  (f : Truncated.Edge (X := (truncation 2).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})) x y)

/-- 閉性から元の全部分複体の安定性を導く。 -/
theorem isStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) := by
  have : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) := ⟨⟨(zeroVertex P hP).vertex,
    (zeroVertex P hP).isZero⟩⟩
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_bicartesian_choices
  · intro x y f
    let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenFiberSquare (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))
    refine ⟨fiberLift P f s (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.fiber_vertices P hP f s), reflects_pushout P _ ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (squareLift P s.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.fiber_vertices P hP f s) ≫ _)
    rw [squareLift_ι]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback s.toZeroTriangle s.isPullback
  · intro x y f
    let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι))
    refine ⟨cofiberLift P f s (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.cofiber_vertices P hP f s), reflects_pullback P _ ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (squareLift P s.square (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FullSubcomplex.cofiber_vertices P hP f s) ≫ _)
    rw [squareLift_ι]
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout s.toZeroTriangle s.isPushout

end FullSubcomplex
end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.3.2"] _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.isStable
attribute [cite HA "1.1.3.3" (partial := stronger-hyp) "仮定：安定準圏の充満部分圏でファイバーにも閉じる、または hX の三角閉性（Lean が強い：HA は余ファイバーとシフトのみ）。結論：前者は充満部分圏の安定性、後者はシフト閉性。余ファイバーの逆シフトからファイバー閉性を導く判定は得られない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.FullSubcomplex.isStable
