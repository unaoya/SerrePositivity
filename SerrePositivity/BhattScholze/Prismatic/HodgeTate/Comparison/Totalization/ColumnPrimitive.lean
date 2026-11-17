module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.Components

/-!
# 積全複体の余輪体の最初の成分を消す

## 概要
一行の完全性で得た原始元を同じ積全複体へ挿入し、先行する零成分を保つ。

## 方針
全微分の二項公式を用いる。原始元の族に線形性や自然性を仮定しない。

## 規約
内部複体の項の有界性は要求しない。使うのは指定した対角線のホモロジーの零性。

## 使われ方
BS 著者版 Lemma 4.22 の、Tot の尾部のコホモロジーの下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R] (K : CochainComplex (Complex R) ℕ)

/-- 一行への挿入の微分は、その行では符号付きの縦微分になる。 -/
theorem insert_d_self (q : ℤ) (n : ℕ) (a : (K.X n).X (q-n)) :
    componentπ K n (q+1) ((total K).d q (q+1) (insert K q n a)) =
      (n : ℤ).negOnePow • ((K.X n).d (q-n) (q+1-n) a) := by
  cases n with
  | zero =>
    rw [differential_zero, insert_component_self]
    simp
  | succ n =>
    rw [differential_succ, insert_component_ne K q (n+1) n (by omega),
      insert_component_self, map_zero, map_zero, zero_add]

/-- 挿入した行より前の成分は、微分を取っても零のままである。 -/
theorem insert_d_below (q : ℤ) (n : ℕ) (a : (K.X n).X (q-n))
    (m : ℕ) (hm : m < n) :
    componentπ K m (q+1) ((total K).d q (q+1) (insert K q n a)) = 0 := by
  cases m with
  | zero =>
    rw [differential_zero, insert_component_ne K q n 0 (by omega), map_zero]
  | succ m =>
    rw [differential_succ, insert_component_ne K q n m (by omega),
      insert_component_ne K q n (m+1) (by omega),
      map_zero, map_zero, map_zero, smul_zero, zero_add]

/-- 全微分の n 成分は、元の n 以下の成分だけで決まる。 -/
theorem differential_component_congr (q : ℤ) (n : ℕ) (x y : (total K).X q)
    (h : ∀ m : ℕ, m ≤ n → componentπ K m q x = componentπ K m q y) :
    componentπ K n (q+1) ((total K).d q (q+1) x) =
      componentπ K n (q+1) ((total K).d q (q+1) y) := by
  cases n with
  | zero => rw [differential_zero, differential_zero, h 0 (by omega)]
  | succ n =>
    rw [differential_succ, differential_succ, h n (by omega), h (n+1) (by omega)]

/-- 最初の非零成分の行が完全なら、その成分を消す挿入原始元がある。 -/
theorem exists_insert_primitive (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0) (n : ℕ)
    (hprev : ∀ m : ℕ, m < n → componentπ K m q x = 0)
    (hn : IsZero ((K.X n).homology (q-n))) :
    ∃ a : (K.X n).X (q-1-n),
      componentπ K n q ((total K).d (q-1) q (insert K (q-1) n a)) =
        componentπ K n q x := by
  let z := (n : ℤ).negOnePow • (componentπ K n q x)
  have hc := first_component_closed K q x hx n hprev
  have hdeg : q+1-(n : ℤ) = (q-(n : ℤ))+1 := by omega
  rw [hdeg] at hc
  have hz : (K.X n).d (q-n) ((q-n)+1) z = 0 := by
    dsimp only [z]
    rw [Units.smul_def, map_zsmul, hc, smul_zero]
  have hindex : (q-(n : ℤ))-1 = q-1-(n : ℤ) := by omega
  have hex := exists_vertical_primitive (K.X n) (q-n) hn z hz
  rw [hindex] at hex
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ?_⟩
  have h := insert_d_self K (q-1) n a
  have hq : q - 1 + 1 = q := by omega
  rw [hq] at h
  rw [ha] at h
  dsimp only [z] at h
  rw [smul_smul, Int.units_mul_self, one_smul] at h
  exact h

/-- 余輪体を一つの境界で修正して、零の先行成分を一行分伸ばす。 -/
theorem kill_first_component (q : ℤ) (x : (total K).X q)
    (hx : (total K).d q (q+1) x = 0) (n : ℕ)
    (hprev : ∀ m : ℕ, m < n → componentπ K m q x = 0)
    (hn : IsZero ((K.X n).homology (q-n))) :
    ∃ a : (K.X n).X (q-1-n),
      (total K).d q (q+1) (x - (total K).d (q-1) q (insert K (q-1) n a)) = 0 ∧
      ∀ m : ℕ, m < n+1 →
        componentπ K m q (x - (total K).d (q-1) q (insert K (q-1) n a)) = 0 := by
  obtain ⟨a, ha⟩ := exists_insert_primitive K q x hx n hprev hn
  refine ⟨a, ?_, ?_⟩
  · have hdd := congrArg (fun f => f (insert K (q-1) n a))
      ((total K).d_comp_d (q-1) q (q+1))
    simp only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at hdd
    rw [map_sub, hx, hdd, sub_self]
  · intro m hm
    by_cases hmn : m < n
    · have hb : componentπ K m q ((total K).d (q-1) q (insert K (q-1) n a)) = 0 := by
        have h := insert_d_below K (q-1) n a m hmn
        have hq : q - 1 + 1 = q := by omega
        rw [hq] at h
        exact h
      rw [map_sub, hprev m hmn, hb, sub_self]
    · have heq : m = n := by omega
      subst m
      rw [map_sub, ha, sub_self]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
