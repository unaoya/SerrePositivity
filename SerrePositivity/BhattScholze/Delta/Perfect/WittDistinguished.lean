module

public import SerrePositivity.BhattScholze.Delta.Perfect.WittDelta
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaRankOne
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion

/-! # Witt環のdistinguished元の係数判定

BS著者公開版Lemma 2.33の具体的なWitt環の場合。
Teichmüller元はrank 1であり、標準δの第0係数は元の第1Witt係数に等しい。
既存の共通Witt単元判定を用い、第1係数でdistinguished性を判定する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- 完全係数環のTeichmüller元はrank 1。すべてのp冪根をTeichmüller写像で持ち上げ、
前段の一般δ環のrank 1定理を適用する。 -/
@[simp] theorem wittDeltaStructure_delta_teichmuller (x : k) :
    (wittDeltaStructure p k).delta (WittVector.teichmuller p x) = 0 := by
  apply DeltaStructure.delta_eq_zero_of_has_pow_roots
  intro n
  obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p ^ n)).2 x
  change y ^ p ^ n = x at hy
  refine ⟨WittVector.teichmuller p y, ?_⟩
  rw [← map_pow, hy]

/-- 標準Witt δの第0係数は元の第1Witt係数。
元を[x₀]+p*yと書き、δの加法・積公式を第0係数で比較する（BS Lemma 2.33）。 -/
theorem wittDeltaStructure_delta_coeff_zero (d : WittVector p k) :
    ((wittDeltaStructure p k).delta d).coeff 0 = d.coeff 1 := by
  let D := wittDeltaStructure p k
  let q : WittVector p k →+* k := WittVector.constantCoeff
  have hqp : q (p : WittVector p k) = 0 := by simp [q, CharP.cast_eq_zero]
  have hm : d - WittVector.teichmuller p (d.coeff 0) ∈
      Ideal.span {(p : WittVector p k)} := by
    apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr
    change q (d - WittVector.teichmuller p (d.coeff 0)) = 0
    rw [map_sub]
    simp only [q, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  have he : d = WittVector.teichmuller p (d.coeff 0) + (p : WittVector p k) * y := by
    linear_combination hy
  have hc : q ((WittVector.teichmuller p (WittVector.teichmuller p (d.coeff 0)) +
      WittVector.teichmuller p ((p : WittVector p k) * y)).coeff 1) = 0 := by
    simp only [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, map_mul, hqp,
      zero_mul, WittVector.teichmuller_zero, add_zero, WittVector.teichmuller_coeff_pos p _ 1
        (by decide)]
  have hδ : q (D.delta d) = q y ^ p := by
    rw [he, D.delta_add, map_add, map_add, hc]
    rw [show D.delta (WittVector.teichmuller p (d.coeff 0)) = 0 from
      wittDeltaStructure_delta_teichmuller p k _]
    rw [map_zero, zero_add, add_zero, D.delta_mul]
    simp only [map_add, map_mul, map_pow, hqp, zero_pow (Fact.out : p.Prime).ne_zero,
      zero_mul, D.map_delta_p q, one_mul, add_zero, zero_add]
  have hd1 : d.coeff 1 = q y ^ p := by
    rw [he, witt_add_coeff_one, WittVector.teichmuller_coeff_pos p _ 1 (by decide)]
    simp only [WittVector.teichmuller_coeff_zero, WittVector.mul_coeff_zero,
      WittVector.coeff_p_zero, zero_mul, WittVector.teichmuller_zero, add_zero,
      WittVector.teichmuller_coeff_pos p _ 1 (by decide), zero_add,
      witt_mul_coeff_one, WittVector.coeff_p_one, zero_pow (Fact.out : p.Prime).ne_zero,
      one_mul, CharP.cast_eq_zero]
    rfl
  exact hδ.trans hd1.symm

/-- 完全係数環のWitt元がdistinguishedであることと第1Witt係数の単元性は同値。
δの第0係数の計算と既存共通Witt単元判定を使う（BS Lemma 2.33のWitt表示）。 -/
theorem wittDeltaStructure_isDistinguished_iff (d : WittVector p k) :
    (wittDeltaStructure p k).IsDistinguished d ↔ IsUnit (d.coeff 1) := by
  constructor
  · intro hd
    have h := hd.map (WittVector.constantCoeff : WittVector p k →+* k)
    simpa only [WittVector.constantCoeff_apply, wittDeltaStructure_delta_coeff_zero] using h
  · intro hd
    apply PerfectoidFrobeniusCriterion.witt_isUnit_of_constantCoeff k p
    rw [wittDeltaStructure_delta_coeff_zero]
    exact hd

/-- Teichmüller展開のpの係数でのdistinguished判定（BS Lemma 2.33）。
Mathlibの展開ではこの係数は逆Frobeniusを第1Witt係数に適用した元。
Frobeniusは単元性を保存・反映するので第1係数判定と同値になる。 -/
theorem wittDeltaStructure_isDistinguished_iff_teichmuller_coefficient (d : WittVector p k) :
    (wittDeltaStructure p k).IsDistinguished d ↔
      IsUnit ((_root_.frobeniusEquiv k p).symm (d.coeff 1)) := by
  apply (wittDeltaStructure_isDistinguished_iff p k d).trans
  simpa only [frobeniusEquiv_symm_pow_p] using
    (isUnit_pow_iff (a := (_root_.frobeniusEquiv k p).symm (d.coeff 1))
      (Fact.out : p.Prime).ne_zero)

end SerrePositivity.BhattScholze
