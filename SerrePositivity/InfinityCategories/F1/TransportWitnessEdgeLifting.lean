module

public import SerrePositivity.InfinityCategories.F1.TransportSquareEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.TransportWitnessRestrictionInner

/-!
概要：表現空間の制限の辺を指定した始点から持ち上げる。
方針：四角形を持ち上げ、分類図式の可逆性で終点の表現条件を回収する。
規約：底は任意、制限する写像は単射。
使われ方：Kerodon Lemma 5.6.8.10 の一次ホーン充填。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：単射への表現の制限は辺を指定始点から持ち上げる。
方針：可逆な分類図式の延長と表現条件の辺に沿う不変性を使う。
規約：終点と制限した辺は厳密に一致する。
使われ方：表現空間の制限の left fibration 性。 -/
lemma transportWitnessRestriction_liftEdge_source {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) [Mono g]
    (x : (transportWitnessSpace p) _⦋0⦌)
    {y : (transportWitnessSpace (pullback.snd p g)) _⦋0⦌}
    (e : SSet.Edge ((transportWitnessRestriction p g).app _ x) y) :
    ∃ L : (Δ[1] : SSet.{u + 1}) ⟶ transportWitnessSpace p,
      stdSimplex.δ 1 ≫ L = SSet.yonedaEquiv.symm x ∧
      L ≫ transportWitnessRestriction p g = SSet.yonedaEquiv.symm e.edge := by
  obtain ⟨R, rfl⟩ := transportWitnessVertex_surjective p x
  let e' : SSet.Edge
      ((transportSquareRestriction p g).app _ (transportSquareVertex R.toSquare)) y.val :=
    e.map (transportWitnessSpaceι (pullback.snd p g))
  have he' : IsInvertibleEdge (e'.map (transportSquareDiagram (pullback.snd p g))) :=
    (transportWitnessEdge_isInvertible (pullback.snd p g) e).map
      (transportWitnessSpaceι (pullback.snd p g) ≫
        transportSquareDiagram (pullback.snd p g))
  obtain ⟨L, hL₀, hLg, hLD⟩ :=
    transportSquareRestriction_liftInvertibleDiagramEdge p g R.toSquare e' he'
  have h₀ : L.app _ (stdSimplex.obj₀Equiv.symm 0) = transportSquareVertex R.toSquare := by
    have h := congrArg SSet.yonedaEquiv hL₀
    simpa only [stdSimplex.δ_one_eq_const, SSet.const_comp,
      SSet.yonedaEquiv_const, Equiv.apply_symm_apply] using h
  let l := (SSet.Edge.ofTruncated homotopyIntervalEdge).map L
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u + 1})) = homotopyIntervalEdge.edge := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hl : IsInvertibleEdge (l.map (transportSquareDiagram p)) := by
    apply (isInvertibleEdge_congr (show (l.map (transportSquareDiagram p)).edge =
      SSet.yonedaEquiv (L ≫ transportSquareDiagram p) from ?_)).mpr hLD
    change (L ≫ transportSquareDiagram p).app _ homotopyIntervalEdge.edge = _
    change (L ≫ transportSquareDiagram p).app (Opposite.op ⦋1⦌)
      homotopyIntervalEdge.edge = _
    rw [← hi, ← SSet.yonedaEquiv_comp]
    simp
  have hx₀ : IsTransportWitnessVertex p (L.app _ (stdSimplex.obj₀Equiv.symm 0)) := by
    rw [h₀]
    exact ⟨R, rfl⟩
  have hx₁ := isTransportWitnessVertex_target p l hx₀ hl
  have hv : ∀ v : (Δ[1] : SSet.{u + 1}) _⦋0⦌, IsTransportWitnessVertex p (L.app _ v) := by
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i
    · exact hx₀
    · exact hx₁
  let W := fullSubcomplexLift (IsTransportWitnessVertex p) L hv
  have hW : W ≫ transportWitnessSpaceι p = L := fullSubcomplexLift_ι _ _ _
  refine ⟨W, ?_, ?_⟩
  · apply (cancel_mono (transportWitnessSpaceι p)).1
    rw [Category.assoc, hW, hL₀, SSet.yonedaEquiv_symm_comp]
    rfl
  · apply (cancel_mono (transportWitnessSpaceι (pullback.snd p g))).1
    rw [Category.assoc, transportWitnessRestriction_ι, ← Category.assoc, hW, hLg,
      SSet.yonedaEquiv_symm_comp]
    rfl

end SerrePositivity.InfinityCategories
