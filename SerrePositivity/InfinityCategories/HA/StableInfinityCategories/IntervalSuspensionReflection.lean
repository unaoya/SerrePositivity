module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorLoopCofiberEvaluation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IntervalSquareFamily
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionEquivalenceOfLoopEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonExt

/-!
概要：懸垂四角形の区間族の終点の可逆性から始点の可逆性を反映する。
方針：各点の同じ懸垂四角形を全部分圏へ移し、終点評価の充満忠実性を使う。
規約：一般安定性・有限余極限を仮定しない。
使われ方：回転後の比較の可逆性から一般零角の比較を戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：関手圏の同じ懸垂四角形を各点の実懸垂四角形へ評価する。
方針：零角の評価と cofiber の点ごとの余極限性を使う。
規約：元の圏の一般安定性は不要。
使われ方：懸垂の区間比較の両端の指定。 -/
def SuspensionSquare.evaluation_of_loopEquivalence {K X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {v : ((ihom K).obj X) _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare v) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) 0 0) where
  square := t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k
  source_eq := rfl
  zero_corner := t.zero_corner.functor_evaluation k
  other_zero := t.other_zero.functor_evaluation k
  isPushout := t.toZeroTriangle.isCofiber_evaluate_of_loopEquivalence s hs hΩ t.isPushout k

/-- 概要：懸垂の区間族で終点が可逆なら、同じ元の始点も可逆。
方針：区間族の実比較辺を懸垂図式の全部分圏に持ち上げ、終点評価で反映する。
規約：同じ実 loop 入力を使い、安定性を先取りしない。
使われ方：一般零角の比較辺を反映する最後の段階。 -/
lemma SuspensionSquare.source_isEquivalencePath_of_target {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    {v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌} (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare v)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex t.vertex) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex v := by
  let t₀ := t.evaluation_of_loopEquivalence s hs hΩ
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
  let t₁ := t.evaluation_of_loopEquivalence s hs hΩ
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge t.square
  let ι := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex).ι
  let H := (hoFunctor.map ι).toFunctor
  let hH := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsSuspensionDiagramVertex (X := X))).toHoFullyFaithful
  let a : (HomotopyCategory.mk t₀.diagramVertex :
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagrams X)) ⟶ HomotopyCategory.mk t₁.diagramVertex :=
    hH.preimage (Truncated.HomotopyCategory.homMk e)
  have ha : H.map a = Truncated.HomotopyCategory.homMk e := hH.map_preimage _
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.suspensionDiagramEvaluation X 1 1)).toFunctor
  have hE := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionDiagramEvaluation_target_isQCatEquivalence_of_loopEquivalence
    s hs hΩ).isFullyFaithful.toHoFullyFaithful
  have htarget : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1)))) :=
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square 1 1).mpr ht
  have hi : IsIso (E.map a) := by
    have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 1 1)) a
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 1 1).map (H.map a) = E.map a at he
    change IsIso (Arrow.mk (E.map a)).hom
    rw [← congrArg Arrow.mk he, ha]
    exact htarget
  have : IsIso a := hE.isIso_of_isIso_map a
  have hsource : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (𝟙 (Δ[1] ⊗ Δ[1] : SSet.{u})) 0 0)))) := by
    change IsIso ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X 0 0).map
      (Truncated.HomotopyCategory.homMk e))
    rw [← ha]
    infer_instance
  have h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.intervalSquareComparisonEdge_isInvertible_evaluate_iff t.square 0 0).mp hsource
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0) at h
  rw [t.source_eq] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
