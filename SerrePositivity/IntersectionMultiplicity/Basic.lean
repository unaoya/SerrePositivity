module

public import SerrePositivity.HomologicalAlgebra.Tor
public import Mathlib.Algebra.BigOperators.Finprod
public import SerrePositivity.HomologicalAlgebra.TorSymmetry
public import SerrePositivity.HomologicalAlgebra.TorBaseChange
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.FlatBaseChange

/-! # Serre の交点重複度

## 概要

Serre の交点重複度 `chi R M N` = Σ_i (-1)^i ℓ_R(Tor_i^R(M, N)) を定め、同型不変性と対称性、極大イデアルを保つ平坦局所拡大でのテンソル積の長さ・各 Tor の長さ・交点重複度の保存を示す。

## 方針

Tor の関手性と変数交換の線形同値から長さの等式を得て交代和へ移す。

## 規約

有限生成性・正則性・有限長性は仮定せず、長さの無限値も含めて述べる。

## 使われ方

IntersectionMultiplicity の全体、Paper の §2・§5。
-/

@[expose] public noncomputable section

universe u

section BasicPart

namespace SerrePositivity

variable (R : Type u) [CommRing R]
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Serre の交点重複度 `χ^R(M, N) = Σ_i (-1)^i ℓ_R(Tor_i^R(M, N))`（整数値）。無限長の項は `0` と
数え、非零項が無限個なら `0`。 -/
noncomputable def chi : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ)

/-- `i > n` で `ℓ(Tor_i) = 0` なら、`χ^R(M, N)` は `i = 0, …, n` の通常の有限和に等しい（`finsum` の台が
`{0, …, n}` に入る）。`Tor` が `dim R` より上で消えることと組み合わせて使う。 -/
lemma chi_eq_sum_range (n : ℕ) (h : ∀ i, n < i → torLength R i M N = 0) :
    chi R M N = ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ) := by
  unfold chi
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hn
  exact hi (by simp [h i (by omega)])

end SerrePositivity

end BasicPart

section EquivalencePart

namespace SerrePositivity

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- 交点重複度は両変数の線形同値で不変。 -/
theorem chi_congr
    {M M' N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : M ≃ₗ[R] M') (e' : N ≃ₗ[R] N') : chi R M N = chi R M' N' := by
  apply finsum_congr
  intro i
  congr 2
  let eTor := (((Tor (ModuleCat R) i).mapIso e.toModuleIso).app (ModuleCat.of R N)) ≪≫
    (((Tor (ModuleCat R) i).obj (ModuleCat.of R M')).mapIso e'.toModuleIso)
  exact congrArg ENat.toNat eTor.toLinearEquiv.length_eq

/-- 交点重複度は二つの加群の交換で不変。 -/
theorem chi_comm (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : chi R M N = chi R N M := by
  apply finsum_congr
  intro i
  congr 2
  exact congrArg ENat.toNat (torComm i (ModuleCat.of R M) (ModuleCat.of R N)).length_eq

end SerrePositivity

end EquivalencePart

section BaseChangePart

namespace SerrePositivity

open IsLocalRing TensorProduct

variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B)
    (M N : Type u) [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

include hm in
/-- 平坦局所拡大は両変数を係数拡大したテンソル積の長さを保つ。 -/
theorem tensorLength_baseChange_of_map_maximalIdeal :
    Module.length B ((B ⊗[A] M) ⊗[B] (B ⊗[A] N)) = Module.length A (M ⊗[A] N) := by
  rw [← (AlgebraTensorModule.distribBaseChange A B M N).length_eq]
  exact length_baseChange_of_map_maximalIdeal A B hm _

include hm in
/-- 平坦局所拡大はすべての次数で Tor の長さを保つ。 -/
theorem torLength_baseChange_of_map_maximalIdeal (i : ℕ) :
    torLength B i (B ⊗[A] M) (B ⊗[A] N) = torLength A i M N := by
  unfold torLength
  rw [(torBaseChangeEquiv A B i M N).length_eq]
  exact length_baseChange_of_map_maximalIdeal A B hm _

include hm in
/-- 平坦局所拡大は交点重複度を保つ。 -/
theorem chi_baseChange_of_map_maximalIdeal :
    chi B (B ⊗[A] M) (B ⊗[A] N) = chi A M N := by
  unfold chi
  apply finsum_congr
  intro i
  rw [torLength_baseChange_of_map_maximalIdeal A B hm M N i]

end SerrePositivity

end BaseChangePart
