module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ComparisonTriangle
public import SerrePositivity.InfinityCategories.F1.CartesianFibration

/-!
概要：cocartesian 辺を、指定した底の三角形の二本の cocartesian 辺へ分解する。
方針：最初の底の辺を cocartesian に持ち上げ、零番二次ホーンを充填して消去則を使う。
規約：元の長辺と底の三角形を厳密に保持する。
使われ方：二次内ホーンで欠ける長辺の保存を、含まれる二辺から反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定された底の三角形上で、同じ cocartesian 長辺を二本の cocartesian 辺へ分解できる。 -/
lemma exists_cocartesianFactorizationTriangle {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (e : E _⦋1⦌) (he : IsCocartesianEdge p e)
    (b : (Δ[2] : SSet.{u}) ⟶ B)
    (hb : SSet.yonedaEquiv.symm e ≫ p = stdSimplex.δ (1 : Fin 3) ≫ b) :
    ∃ t : (Δ[2] : SSet.{u}) ⟶ E,
      t ≫ p = b ∧ stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm e ∧
      IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ t)) ∧
      IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 0 ≫ t)) := by
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫ stdSimplex.δ 2 =
      stdSimplex.δ 1 ≫ stdSimplex.δ (1 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hs : stdSimplex.δ 1 ≫ (stdSimplex.δ 2 ≫ b) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) (E.δ 1 e)) := by
    rw [← Category.assoc, hv, Category.assoc, ← hb, ← Category.assoc,
      stdSimplex.δ_comp_yonedaEquiv_symm, SSet.yonedaEquiv_symm_comp]
  obtain ⟨a, ha, hap, hac⟩ := CocartesianFibration.mem (p := p) |>.2
    (E.δ 1 e) (stdSimplex.δ 2 ≫ b) hs
  obtain ⟨h, hh₂, hh₁⟩ := horn₂₀.isPushout.exists_desc a (SSet.yonedaEquiv.symm e) (by
    rw [ha, stdSimplex.δ_comp_yonedaEquiv_symm])
  have sq : CommSq h (horn 2 0).ι p b := by
    constructor
    apply horn₂₀.isPushout.hom_ext
    · simp only [← Category.assoc, hh₂, horn.ι_ι]
      exact hap
    · simp only [← Category.assoc, hh₁, horn.ι_ι]
      exact hb
  have hfirst : h.app (Opposite.op ⦋1⦌) (initialHornEdge 0) = SSet.yonedaEquiv a := by
    have ht := congrArg SSet.yonedaEquiv hh₂
    rw [SSet.yonedaEquiv_comp] at ht
    have hi : SSet.yonedaEquiv horn₂₀.ι₀₁ = initialHornEdge 0 := by
      apply Subtype.ext
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rwa [hi] at ht
  have := hac 0 h b hfirst sq
  let t := sq.lift
  have ht₂ : stdSimplex.δ 2 ≫ t = a := by
    rw [← horn.ι_ι_assoc 0 2 (by decide), sq.fac_left]
    exact hh₂
  have ht₁ : stdSimplex.δ 1 ≫ t = SSet.yonedaEquiv.symm e := by
    rw [← horn.ι_ι_assoc 0 1 (by decide), sq.fac_left]
    exact hh₁
  have htc : IsCocartesianEdge p (SSet.yonedaEquiv (stdSimplex.δ 2 ≫ t)) := by
    rw [ht₂]
    exact hac
  refine ⟨t, sq.fac_right, ht₁, htc, ?_⟩
  apply kanIsCocartesianEdge_triangle_second_of_first_long t p htc
  rw [ht₁, Equiv.apply_symm_apply]
  exact he

end SerrePositivity.InfinityCategories
