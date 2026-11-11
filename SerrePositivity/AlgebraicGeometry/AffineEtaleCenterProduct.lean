module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：有限個の局所中心を同時に因子として持つアフィン基底の中心を作る。
方針：個別の降下で得た中心を掛け、境界冪は各指数の和を取る。
規約：局所チャートの環と写像は添字ごとに異なってよい。
使われ方：Stacks 0814 の有限個の étale チャートを一つの基底ブローアップで支配する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped BigOperators

/--
概要：各局所中心が基底中心の拡張の因子になるなら、一つの基底中心で
有限個の局所中心を同時に因子として含められる。
方針：個別の基底中心の積を取り、各チャートでは対応する一因子を分ける。
規約：各基底中心は境界元のある冪を含む。
使われ方：étale 局所で得た平坦化ブローアップを共通に支配する中心の構成。
-/
theorem exists_common_affine_center_of_factors
    {R ι : Type*} [CommRing R] [IsNoetherianRing R] [Finite ι]
    (B : ι → Type*) [∀ i, CommRing (B i)] (f : ∀ i, R →+* B i)
    (J : ∀ i, Ideal (B i)) (a : R)
    (h : ∀ i, ∃ (I : Ideal R) (n : ℕ), a ^ n ∈ I ∧
      ∃ K : Ideal (B i), K.FG ∧ I.map (f i) = J i * K) :
    ∃ I : Ideal R, I.FG ∧ (∃ n : ℕ, a ^ n ∈ I) ∧
      ∀ i, ∃ K : Ideal (B i), K.FG ∧ I.map (f i) = J i * K := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose I n hn K hK heq using h
  refine ⟨∏ i, I i, IsNoetherian.noetherian _, ⟨∑ i, n i, ?_⟩, ?_⟩
  · rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod (fun i _ => hn i)
  · intro i
    let L := ∏ j ∈ Finset.univ.erase i, I j
    have hL : L.FG := IsNoetherian.noetherian _
    refine ⟨K i * L.map (f i), (hK i).mul (hL.map _), ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ I (Finset.mem_univ i)]
    change (I i * L).map (f i) = _
    rw [Ideal.map_mul, heq i, mul_assoc]

end SerrePositivity.AlgebraicGeometry
