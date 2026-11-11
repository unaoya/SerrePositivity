module

public import SerrePositivity.KST.LocalizingInvariants.TammeOreCartesianSpanLift

/-!
概要：任意の固定第一終点 span 頂点へ入る Tamme 分母には、終点を保つ cartesian lift がある。
方針：元の頂点の span 表示に普遍 Ore lift を適用し、第一終点の厳密な等式で fiber へ戻す。
規約：終点は元の頂点そのもの。使われ方：分母に沿う span 族の局所 cartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma exists_tammeMarkedSpanCartesianLift (x : (laxCategory p q).obj _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x) _⦋0⦌)
    {y : (laxCategory p q).obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x).app
        (Opposite.op ⦋0⦌) v)) (hs : s.edge ∈ tammeLocalizingEdges p q) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x,
      stdSimplex.δ (0 : Fin 2) ≫ F = SSet.yonedaEquiv.symm v ∧
      F ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x =
        SSet.yonedaEquiv.symm s.edge ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x)
        (SSet.yonedaEquiv F) := by
  let X := (laxCategory p q).obj
  let W := tammeLocalizingEdges p q
  let S := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm v.val.val
  have hS : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S = v.val.val := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v.val.val
  have hSW : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ W := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v.val
    change spanLeftEdge v.val.val ∈ W at h
    rw [← hS] at h
    exact h
  let t := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have ht : t = x := by
    have hv : (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = x := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero] using v.property
    rw [show (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = t from ?_] at hv
    · exact hv
    · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₁).app X).app _ v.val.val) = t
      rw [← hS]
      rfl
  have htarget : X.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x).app (Opposite.op ⦋0⦌) v := by
    rw [intervalMap_target]
    change (horn₂₀.ι₀₂ ≫ S).app _ _ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₂).app X).app _ v.val.val)
    rw [← hS]
    rfl
  let s' : Truncated.Edge (X := (truncation 2).obj X) y
      (X.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))) :=
    ⟨s.edge, s.src_eq, s.tgt_eq.trans htarget.symm⟩
  obtain ⟨R, G, hR, _hRt, hG₁, hGt, hGr, _hGc⟩ :=
    exists_tammeOreCartesianSpanLift p q S hSW s' hs
  let M : (Δ[1] : SSet.{u}) ⟶ markedSpans X W := G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) t
  have hMs : M ≫ markedSpanSource X W = SSet.const x := by
    dsimp only [M]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, ht]
  let F : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanSource X W) x M hMs
  have hF : F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x = M := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  let r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W
  have hFr : F ≫ r = M ≫ markedSpanInclusion X W := by
    dsimp only [r]
    rw [← Category.assoc, hF]
  refine ⟨F, ?_, ?_, ?_⟩
  · have : Mono r := by dsimp [r, markedSpanInclusion]; infer_instance
    apply (cancel_mono r).mp
    rw [Category.assoc, hFr]
    change stdSimplex.δ (0 : Fin 2) ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) t ≫
      markedSpanInclusion X W = SSet.yonedaEquiv.symm v ≫ r
    rw [hG₁, hS, SSet.yonedaEquiv_symm_zero, SSet.const_comp]
    rfl
  · change (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = _
    rw [hF]
    exact hGt
  · apply isCartesianEdge_markedSpanFamilyProjection_of_pullback
    rw [SSet.yonedaEquiv.symm_apply_apply]
    have hr : F ≫ r ≫ (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R := by
      rw [← Category.assoc, hFr]
      exact hGr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (uncurry (F ≫ r ≫ (pre horn₂₀.ι₀₂).app X))
    rw [hr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily, uncurry_curry]
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isPullbackSquare_iff_transpose R).mp hR

end SerrePositivity.KST.LocalizingInvariants
