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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma exists_tammeMarkedSpanCartesianLift (x : (laxCategory p q).obj _⦋0⦌)
    (v : (markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x) _⦋0⦌)
    {y : (laxCategory p q).obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y
      ((markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x).app
        (Opposite.op ⦋0⦌) v)) (hs : s.edge ∈ tammeLocalizingEdges p q) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶
        markedSpanFamily (laxCategory p q).obj (tammeLocalizingEdges p q) x,
      stdSimplex.δ (0 : Fin 2) ≫ F = SSet.yonedaEquiv.symm v ∧
      F ≫ markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x =
        SSet.yonedaEquiv.symm s.edge ∧
      IsCartesianEdge
        (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x)
        (SSet.yonedaEquiv F) := by
  let X := (laxCategory p q).obj
  let W := tammeLocalizingEdges p q
  let S := (functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm v.val.val
  have hS : functorVertex S = v.val.val := (functorVertexEquiv _ _).apply_symm_apply v.val.val
  have hSW : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ W := by
    have h := fullSubcomplexOnVertices_vertex v.val
    change spanLeftEdge v.val.val ∈ W at h
    rw [← hS] at h
    exact h
  let t := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  have ht : t = x := by
    have hv : (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = x := by
      simpa only [PinchedHom.constant_zero] using v.property
    rw [show (markedSpanSource X W).app (Opposite.op ⦋0⦌) v.val = t from ?_] at hv
    · exact hv
    · change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₁).app X).app _ v.val.val) = t
      rw [← hS]
      rfl
  have htarget : X.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S)) =
      (markedSpanFamilyProjection X W x).app (Opposite.op ⦋0⦌) v := by
    rw [intervalMap_target]
    change (horn₂₀.ι₀₂ ≫ S).app _ _ =
      (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
        (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₂).app X).app _ v.val.val)
    rw [← hS]
    rfl
  let s' : Truncated.Edge (X := (truncation 2).obj X) y
      (X.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))) :=
    ⟨s.edge, s.src_eq, s.tgt_eq.trans htarget.symm⟩
  obtain ⟨R, G, hR, _hRt, hG₁, hGt, hGr, _hGc⟩ :=
    exists_tammeOreCartesianSpanLift p q S hSW s' hs
  let M : (Δ[1] : SSet.{u}) ⟶ markedSpans X W := G ≫ vertexFiberι (markedSpanSource X W) t
  have hMs : M ≫ markedSpanSource X W = SSet.const x := by
    dsimp only [M]
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, ht]
  let F : (Δ[1] : SSet.{u}) ⟶ markedSpanFamily X W x :=
    vertexFiberLift (markedSpanSource X W) x M hMs
  have hF : F ≫ vertexFiberι (markedSpanSource X W) x = M := vertexFiberLift_ι _ _ _ _
  let r : markedSpanFamily X W x ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
    vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W
  have hFr : F ≫ r = M ≫ markedSpanInclusion X W := by
    dsimp only [r]
    rw [← Category.assoc, hF]
  refine ⟨F, ?_, ?_, ?_⟩
  · have : Mono r := by dsimp [r, markedSpanInclusion]; infer_instance
    apply (cancel_mono r).mp
    rw [Category.assoc, hFr]
    change stdSimplex.δ (0 : Fin 2) ≫ G ≫ vertexFiberι (markedSpanSource X W) t ≫
      markedSpanInclusion X W = SSet.yonedaEquiv.symm v ≫ r
    rw [hG₁, hS, SSet.yonedaEquiv_symm_zero, SSet.const_comp]
    rfl
  · change (F ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = _
    rw [hF]
    exact hGt
  · apply isCartesianEdge_markedSpanFamilyProjection_of_pullback
    rw [SSet.yonedaEquiv.symm_apply_apply]
    have hr : F ≫ r ≫ (pre horn₂₀.ι₀₂).app X = squareArrowFamily R := by
      rw [← Category.assoc, hFr]
      exact hGr
    change IsPullbackSquare (uncurry (F ≫ r ≫ (pre horn₂₀.ι₀₂).app X))
    rw [hr, _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.squareArrowFamily, uncurry_curry]
    exact (isPullbackSquare_iff_transpose R).mp hR

end SerrePositivity.KST.LocalizingInvariants
