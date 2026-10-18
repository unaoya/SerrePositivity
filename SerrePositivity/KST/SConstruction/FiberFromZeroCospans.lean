module
public import SerrePositivity.KST.SConstruction.ZeroCospanChoices
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-! # 零脚の cospan の極限から fiber を構成する
概要：零対象からの脚を持つ cospan の極限を、指定された辺の fiber 正方形にする。
方針：零対象から終点への辺を貼り合わせ、錐と正方形の同型で戻す。
規約：安定性を仮定しない。使われ方：関手圏の fiber の存在。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：零脚つき cospan の極限があれば各辺の fiber 正方形が存在する。
方針：零対象から終点への辺で cospan を作り、その極限錐を正方形に戻す。
規約：元の辺を厳密に保つ。使われ方：点ごとの極限から関手圏の fiber へ。 -/
lemma fiberSquare_nonempty_of_zeroCospan_limits {X : SSet.{u}} [Quasicategory X]
    [HasZeroVertex X]
    (h : ∀ p : (horn 2 2 : SSet.{u}) ⟶ X,
      IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p)) → HasLimit p)
    {x y : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (FiberSquare f) := by
  let z := chosenZeroVertex X
  obtain ⟨g⟩ := z.isInitial.nonempty_edge y
  let d := SSet.yonedaEquiv.symm f.edge
  let e := SSet.yonedaEquiv.symm g.edge
  have he : stdSimplex.δ (0 : Fin 2) ≫ d = stdSimplex.δ (0 : Fin 2) ≫ e :=
    (edgeSimplex_target f).trans (edgeSimplex_target g).symm
  let p := horn₂₂.isPushout.desc d e he
  have hp₀ : horn₂₂.ι₀₂ ≫ p = d := horn₂₂.isPushout.inl_desc _ _ _
  have hp₁ : horn₂₂.ι₁₂ ≫ p = e := horn₂₂.isPushout.inr_desc _ _ _
  have hpz : IsZeroSourceArrow (functorVertex (horn₂₂.ι₁₂ ≫ p)) := by
    rw [hp₁]
    change IsZeroVertex ((evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))).app
      (Opposite.op ⦋0⦌) (functorVertex e))
    rw [evaluateFunctorAt_functorVertex]
    have hz := congrArg SSet.yonedaEquiv (edgeSimplex_source g)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hz
    have hδ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    rw [hδ] at hz
    exact hz.symm ▸ z.isZero
  obtain ⟨c, hc⟩ := h p hpz
  let F := cospanConeSquareIso.inv ≫ c.val
  have hFp : cospanSquareBoundary ≫ F = p := by
    dsimp only [F, cospanSquareBoundary]
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact c.property
  have hFt : squareTopEdge ≫ F = e := by
    rw [← cospanSquareBoundary_topEdge, Category.assoc, hFp, hp₁]
  refine ⟨{
    square := F
    zero_corner := ?_
    right_edge := ?_
    isPullback := ?_ }⟩
  · have hv := ConcreteCategory.congr_hom (NatTrans.congr_app hFt (Opposite.op ⦋0⦌))
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))
    change squareVertex F 0 1 = _ at hv
    rw [hv]
    have hz := congrArg SSet.yonedaEquiv (edgeSimplex_source g)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hz
    have hδ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) :
        (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (0 : Fin 2) := by decide
    rw [hδ] at hz
    exact hz.symm ▸ z.isZero
  · rw [← cospanSquareBoundary_rightEdge, Category.assoc, hFp, hp₀]
  · apply (isLimitCone_iff_of_diagram_eq (c := pullbackCone F) (d := c) hFp _).2 hc
    dsimp only [pullbackCone, F]
    exact Iso.hom_inv_id_assoc _ _

end SerrePositivity.KST.SConstruction
