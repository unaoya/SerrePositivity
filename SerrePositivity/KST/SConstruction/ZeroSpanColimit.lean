module
public import SerrePositivity.KST.SConstruction.ColimitComparison

/-! # 零対象だけからなる span の普遍余錐
概要：全入力が零対象なら、その普遍余錐の全頂点も零対象。
方針：定値零図式の普遍余錐と関手全体を同型で比較する。
規約：入力の零対象や零射を厳密に同じとは仮定しない。使われ方：gapped の零対角の閉性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零対象だけの span の普遍余錐は関手圏の零対象。
方針：定値零四角形の余錐との関手同型を、図式の零対象性から構成する。
規約：安定性は不要。使われ方：完成した全頂点の零対象性。 -/
lemma zeroSpanColimit_functorVertex_isZero {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (p.app (Opposite.op ⦋0⦌) a)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C
  let Z : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ C := SSet.const z.vertex
  have hZ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare Z := by
    have h := isPushoutSquare_fst (SSet.const z.vertex : (Δ[1] : SSet.{u}) ⟶ C)
    rwa [SSet.comp_const] at h
  have hpZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan Z)) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ SSet.const z.vertex))
    rw [SSet.comp_const]
    exact functor_const_isZeroVertex z.vertex z.isZero
  have hpF := isZeroVertex_functorVertex_of_pointwise p hp
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan Z) p :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.zeroVertexIso ⟨_, hpZ.1, hpZ.2⟩ ⟨_, hpF.1, hpF.2⟩
  let E := colimitCoconeIsoOfDiagramIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone Z) c hZ hc e
  have hcz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone Z).val) := by
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ SSet.const z.vertex))
    rw [SSet.comp_const]
    exact functor_const_isZeroVertex z.vertex z.isZero
  exact hcz.of_vertexIso E

/-- 概要：零対象だけの span の普遍余錐の全頂点は零対象。
方針：余錐全体の関手の零対象性を各点で評価する。
規約：錐頂点も境界の全頂点も含む。使われ方：二方向補完の全行の零脚。 -/
lemma zeroSpanColimit_all_vertices_zero {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hp : ∀ a : (horn 2 0 : SSet.{u}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (p.app (Opposite.op ⦋0⦌) a))
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (horn 2 0 : SSet.{u}) Δ[0]) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (c.val.app (Opposite.op ⦋0⦌) v) := by
  have h := isZeroVertex_evaluateFunctorAt (zeroSpanColimit_functorVertex_isZero c hc hp) v
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h

end SerrePositivity.KST.SConstruction
