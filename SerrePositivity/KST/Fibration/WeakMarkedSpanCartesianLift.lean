module
public import SerrePositivity.KST.Fibration.WeakOreCartesianSpanLift

/-! # 元の固定第一終点 span の任意の頂点への W 分母の cartesian lift -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q)

include h in
lemma exists_weakMarkedSpanCartesianLift (x : B.obj _⦋0⦌)
    (v : (markedSpanFamily B.obj (weakEquivalences i) x) _⦋0⦌)
    {y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      ((markedSpanFamilyProjection B.obj (weakEquivalences i) x).app
        (Opposite.op ⦋0⦌) v)) (hs : s.edge ∈ weakEquivalences i) :
    ∃ F : (Δ[1] : SSet.{u}) ⟶
        markedSpanFamily B.obj (weakEquivalences i) x,
      stdSimplex.δ (0 : Fin 2) ≫ F = SSet.yonedaEquiv.symm v ∧
      F ≫ markedSpanFamilyProjection B.obj (weakEquivalences i) x =
        SSet.yonedaEquiv.symm s.edge ∧
      IsCartesianEdge
        (markedSpanFamilyProjection B.obj (weakEquivalences i) x)
        (SSet.yonedaEquiv F) := by
  let X := B.obj
  let W := weakEquivalences i
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
    exists_weakOreCartesianSpanLift h S hSW s' hs
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


end SerrePositivity.KST.Fibration
