module

public import SerrePositivity.AlgebraicGeometry.BoundaryIdempotentNumerators
public import Mathlib.RingTheory.Idempotents

/-!
概要：KST §5、Stacks Lemma 31.35.5 の境界外の有限分割の共通分母消去。
方針：有限個の分母の指数の上限を取り、正則元の局所化の単射性で直交性と総和を戻す。
規約：空の族の場合の零環も含む。
使われ方：有限個の階数部分を一段の blowup 中心で分離する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] [Fintype ι]

/--
概要：局所化環の完全直交冪等元の有限族に、総和が境界冪で直交する境界内の分子を選べる。
方針：各分母を共通指数に揃え、境界元をさらに一回掛け、局所化の単射性で等式を戻す。
規約：KST §5、Stacks Lemma 31.35.5、基礎環は Noether と仮定しない。
使われ方：有限分割のための実際の有限生成中心の生成族。
-/
theorem exists_finite_orthogonal_boundary_numerators (f : R) (hf : IsRegular f)
    (e : ι → Localization.Away f) (he : CompleteOrthogonalIdempotents e) :
    ∃ (N : ℕ) (a : ι → R), 0 < N ∧ (∀ i, f ∣ a i) ∧
      (∑ i, a i) = f ^ N ∧ Pairwise (fun i j => a i * a j = 0) ∧
      ∀ i, algebraMap R (Localization.Away f) (a i) =
        e i * algebraMap R (Localization.Away f) f ^ N := by
  classical
  let F := Localization.Away f
  let φ : R →+* F := algebraMap R F
  have hφ : Function.Injective φ :=
    IsLocalization.injective F (Submonoid.powers_le.mpr
      (isRegular_iff_mem_nonZeroDivisors.mp hf))
  choose n b hb using fun i => IsLocalization.Away.surj f (e i)
  let d := Finset.univ.sup n
  have hn (i : ι) : n i ≤ d := Finset.le_sup (Finset.mem_univ i)
  let a : ι → R := fun i => b i * f ^ (d - n i) * f
  have ha (i : ι) : φ (a i) = e i * φ f ^ (d + 1) := by
    change φ (b i * f ^ (d - n i) * f) = _
    have hbi : φ (b i) = e i * φ f ^ n i := (hb i).symm
    rw [map_mul, map_mul, map_pow, hbi]
    calc
      _ = e i * (φ f ^ n i * φ f ^ (d - n i)) * φ f := by ring
      _ = e i * φ f ^ (d + 1) := by
        rw [← pow_add, Nat.add_sub_of_le (hn i), pow_succ]
        ring
  refine ⟨d + 1, a, Nat.succ_pos d, fun i => dvd_mul_left f _, ?_, ?_, ha⟩
  · apply hφ
    rw [map_sum, map_pow]
    simp only [ha, ← Finset.sum_mul, he.complete, one_mul]
  · intro i j hij
    apply hφ
    rw [map_mul, ha, ha, map_zero]
    calc
      (e i * φ f ^ (d + 1)) * (e j * φ f ^ (d + 1)) =
          (e i * e j) * (φ f ^ (d + 1)) ^ 2 := by ring
      _ = 0 := by rw [he.ortho hij, zero_mul]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
