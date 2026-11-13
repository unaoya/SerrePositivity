module

public import SerrePositivity.EInfinity.PowerOperation.CyclicResolutionHomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# 自明な離散係数での完全周期 Hom の微分

DAG XIII Construction 2.2.6 の指定係数類の模型比較の補助。
同じ周期解像度の各 Hom を、左正則表現の評価で係数加群へ同定する。
自明作用かつ標数 p の場合は、同じ Hom 微分が全次数で零となる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (p : ℕ) [NeZero p] {k : Type u} [CommRing k] [CharP k p]
variable (A : Rep.{u} k (PowerOperationCyclicGroup.{u} p)) [A.IsTrivial]

/-- 自明係数への同変射は、同じ完全周期微分を零に送る。 -/
lemma cyclicResolution_d_comp (i j : ℤ)
    (f : (powerOperationCompleteResolution p k).X j ⟶ A) :
    (powerOperationCompleteResolution p k).d i j ≫ f = 0 := by
  dsimp [powerOperationCompleteResolution, cyclicTateComplex, CochainComplex.of.d]
  split_ifs with h
  · subst j
    simp only [Category.comp_id]
    rw [cyclicTateDifferential_natural,
      cyclicTateDifferential_trivial A p (powerOperationCyclicGroup_card p),
      Limits.comp_zero]
  · simp

/-- 離散係数への完全周期 Hom 複体の各次数の実線形同値。 -/
def cyclicResolutionSingleDegreeEquiv (i : ℤ) :
    Cochain (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A) i ≃ₗ[k] A :=
  (Cochain.toSingleLinearEquiv (show -i + i = (0 : ℤ) by omega)).trans
    (Rep.leftRegularHomEquiv A)

/-- 同じ Hom 複体は、自明作用の離散係数では全次数の微分が零。 -/
lemma cyclicResolutionSingleHom_d (i j : ℤ) :
    (CochainComplex.linearHomComplex k (powerOperationCompleteResolution p k)
      ((singleFunctor (Rep.{u} k (PowerOperationCyclicGroup.{u} p)) 0).obj A)).d i j = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let f := Cochain.toSingleEquiv (show -i + i = (0 : ℤ) by omega) z
  have hz : z = Cochain.toSingleMk f (show -i + i = (0 : ℤ) by omega) := by
    exact (Cochain.toSingleMk_toSingleEquiv _ _).symm
  change δ i j z = 0
  rw [hz, Cochain.δ_toSingleMk _ _ j (-j) (by omega), cyclicResolution_d_comp]
  simp

end SerrePositivity.EInfinity.PowerOperation
