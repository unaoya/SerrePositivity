module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.Composition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornComparison

/-!
概要：既存の型つき辺の合成は、同じcocartesian輸送のホーン充填条件を保つ。
方針：既存の合成二単体を全単体として表示し、既存の長辺の合成則を使う。
規約：Kerodon Corollary 5.1.2.4（Tag 01TS）、HTT §2.4.1の既存構成の計算法則。
使われ方：S8 の大域比較と右Kan輸送の同じ合成辺を評価する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 指定された二つのcocartesianな型つき辺の、既存の同じ合成もcocartesian。 -/
lemma hasCocartesianHornLifting_comp {E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (p : E ⟶ B) [InnerFibration p] {x y z : E _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj E) x y)
    (f : Truncated.Edge (X := (truncation 2).obj E) y z)
    (he : HasCocartesianHornLifting p e) (hf : HasCocartesianHornLifting p f) :
    HasCocartesianHornLifting p (e.comp f) := by
  let t := Truncated.Edge.compStruct e f
  let T : (Δ[2] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm t.simplex
  have h₂ : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ T) = e.edge := by
    dsimp only [T]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₂
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) = f.edge := by
    dsimp only [T]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₀
  have h₁ : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) = (e.comp f).edge := by
    dsimp only [T]
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₁
  have h := isCocartesianEdge_triangle_longEdge T p
  rw [h₂, h₀, h₁] at h
  exact (isCocartesianEdge_iff_hasCocartesianHornLifting p (e.comp f)).mp
    (h ((isCocartesianEdge_iff_hasCocartesianHornLifting p e).mpr he)
      ((isCocartesianEdge_iff_hasCocartesianHornLifting p f).mpr hf))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
