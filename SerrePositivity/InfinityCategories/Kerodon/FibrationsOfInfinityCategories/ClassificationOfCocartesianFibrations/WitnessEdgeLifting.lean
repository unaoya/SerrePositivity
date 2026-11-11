module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareEquivalenceLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessRestrictionInner

/-!
概要：表現空間の制限の辺を指定した始点から持ち上げる。
方針：四角形を持ち上げ、分類図式の可逆性で終点の表現条件を回収する。
規約：底は任意、制限する写像は単射。
使われ方：Kerodon Lemma 5.6.8.10（Tag 02SK） の一次ホーン充填。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdgeLifting

local instance {E B D : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p g) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：単射への表現の制限は辺を指定始点から持ち上げる。
方針：可逆な分類図式の延長と表現条件の辺に沿う不変性を使う。
規約：終点と制限した辺は厳密に一致する。
使われ方：表現空間の制限の left fibration 性。 -/
lemma transportWitnessRestriction_liftEdge_source {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (g : D ⟶ B) [Mono g]
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p) _⦋0⦌)
    {y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (pullback.snd p g)) _⦋0⦌}
    (e : SSet.Edge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g).app _ x) y) :
    ∃ L : (Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace p,
      stdSimplex.δ 1 ≫ L = SSet.yonedaEquiv.symm x ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction p g = SSet.yonedaEquiv.symm e.edge := by
  obtain ⟨R, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex_surjective p x
  let e' : SSet.Edge
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction p g).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare)) y.val :=
    e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.snd p g))
  have he' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e'.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessEdge_isInvertible (pullback.snd p g) e).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.snd p g) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (pullback.snd p g))
  obtain ⟨L, hL₀, hLg, hLD⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareRestriction_liftInvertibleDiagramEdge p g R.toSquare e' he'
  have h₀ : L.app _ (stdSimplex.obj₀Equiv.symm 0) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareVertex R.toSquare := by
    have h := congrArg SSet.yonedaEquiv hL₀
    simpa only [stdSimplex.δ_one_eq_const, SSet.const_comp,
      SSet.yonedaEquiv_const, Equiv.apply_symm_apply] using h
  let l := (SSet.Edge.ofTruncated _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge).map L
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p)) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show (l.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p)).edge =
      SSet.yonedaEquiv (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p) from ?_)).mpr hLD
    change (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p).app _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = _
    change (L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram p).app (Opposite.op ⦋1⦌)
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge = _
    rw [← hi, ← SSet.yonedaEquiv_comp]
    simp
  have hx₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p (L.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
    rw [h₀]
    exact ⟨R, rfl⟩
  have hx₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isTransportWitnessVertex_target p l hx₀ hl
  have hv : ∀ v : (Δ[1] : SSet.{u + 1}) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p (L.app _ v) := by
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i
    · exact hx₀
    · exact hx₁
  let W := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsTransportWitnessVertex p) L hv
  have hW : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  refine ⟨W, ?_, ?_⟩
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι p)).1
    rw [Category.assoc, hW, hL₀, SSet.yonedaEquiv_symm_comp]
    rfl
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (pullback.snd p g))).1
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessRestriction_ι, ← Category.assoc, hW, hLg,
      SSet.yonedaEquiv_symm_comp]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessEdgeLifting
