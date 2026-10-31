module

public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# 正則生成列を持つ局所環の正規性

## 証明

分数体の整元 `x` に対して有限代数 `R[x]` を取り、`x` による乗法を考える。
有限自由分解によるトレースの降下から、この乗法の分数体上のトレースは `R` に属する。
分数体へ係数拡大した `R[x]` は分数体そのものであり、そのトレースは `x` である。
したがって `x` は `R` の像に入る。

正則生成列を明示する一般定理と、正則局所環への適用はともに証明済み。
正則パラメータの正則性を通じ、ガロア正規化と §2 の共通分母に用いる。
-/

public section

universe u

namespace SerrePositivity

open scoped TensorProduct

/-- 極大イデアルが正則列で生成されるネーター局所整域は整閉である。
有限代数 `R[x]` の乗法のトレースを有限自由分解に沿って基底へ降ろす。 -/
theorem isIntegrallyClosed_of_regular_generators
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R) : IsIntegrallyClosed R := by
  classical
  let K := FractionRing R
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  let B := Algebra.adjoin R ({x} : Set K)
  let : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hx
  let xb : B := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  let f : B →ₗ[R] B := Algebra.lmul R B xb
  let m : K ⊗[R] B →ₐ[K] K :=
    Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId K K) B.val
  have hm : Function.Bijective m := by
    constructor
    · have hi := Module.Flat.lTensor_preserves_injective_linearMap
        (M := K) B.val.toLinearMap Subtype.val_injective
      have heq : m.toLinearMap = (Algebra.TensorProduct.lmulEquiv R K).toLinearMap.comp
          (B.val.toLinearMap.baseChange K) := by
        ext b
        rfl
      rw [show Function.Injective m ↔ Function.Injective m.toLinearMap from Iff.rfl, heq]
      exact (Algebra.TensorProduct.lmulEquiv R K).injective.comp hi
    · intro a
      exact ⟨a ⊗ₜ[R] (1 : B), by simp [m]⟩
  let e : K ⊗[R] B ≃ₗ[K] K := (AlgEquiv.ofBijective m hm).toLinearEquiv
  have hf : (f.baseChange K) = e.symm.toLinearMap.comp ((x • LinearMap.id).comp e.toLinearMap) := by
    ext b
    apply e.injective
    change e (f.baseChange K (1 ⊗ₜ[R] b)) = e (e.symm (x * e (1 ⊗ₜ[R] b)))
    rw [e.apply_symm_apply]
    change 1 * (x * (b : K)) = x * (1 * (b : K))
    ring
  have ht : LinearMap.trace K (K ⊗[R] B) (f.baseChange K) = x := by
    rw [hf, LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    simp
  obtain ⟨r, hr⟩ := trace_baseChange_mem_range_of_regular_generators
    (K := K) rs hreg hgen (ModuleCat.of R B) f
  exact ⟨r, hr.trans ht⟩

/-- 正則局所環は整閉である。証明済みの正則パラメータの正則性を使い、
整域性・有限自由分解・トレースを通じた正規性の導出は証明する。 -/
theorem isIntegrallyClosed_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : IsIntegrallyClosed R := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators R
  let : IsDomain R := isDomain_of_regular_generators rs hreg hgen
  exact isIntegrallyClosed_of_regular_generators R rs hreg hgen

end SerrePositivity
