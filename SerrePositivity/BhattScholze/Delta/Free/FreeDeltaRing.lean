module

public import SerrePositivity.BhattScholze.Delta.DeltaFrobenius
public import SerrePositivity.BhattScholze.Delta.DeltaSectionNaturality
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.CharP.Quotient

/-! # 整数係数の自由δ環

変数x_(s,n)を持つ整数多項式環にφ(x_(s,n))=x_(s,n)^p+p*x_(s,n+1)を与える。
BS著者版Lemma 2.11の整数係数の構成。原典のZ_(p)係数への局所化と
Frobeniusの忠実平坦性は、このモジュールで完成したとはしない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (σ : Type u)

/-- 変数x_(s,n)の整数多項式環。δ^n(x_s)をx_(s,n)として実現する。 -/
abbrev FreeDeltaRing := MvPolynomial (σ × ℕ) ℤ

/-- 自由δ環のFrobenius持上げ候補。整数は固定し、各変数をx^p+p*次の変数へ送る。 -/
def freeDeltaFrobenius : FreeDeltaRing σ →+* FreeDeltaRing σ :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun v ↦
    MvPolynomial.X v ^ p + (p : FreeDeltaRing σ) * MvPolynomial.X (v.1, v.2 + 1))

omit [Fact p.Prime] in
/-- 自由δ環のFrobenius候補の生成元上での値。 -/
@[simp] theorem freeDeltaFrobenius_X (s : σ) (n : ℕ) :
    freeDeltaFrobenius p σ (MvPolynomial.X (s, n)) =
      MvPolynomial.X (s, n) ^ p + (p : FreeDeltaRing σ) * MvPolynomial.X (s, n + 1) := by
  simp [freeDeltaFrobenius]

/-- 整数多項式環ではpの乗法が単射。δ構造の復元でpを消去するために使う。 -/
theorem freeDeltaRing_p_mul_injective :
    Function.Injective (fun x : FreeDeltaRing σ ↦ (p : FreeDeltaRing σ) * x) := by
  intro x y hxy
  change (p : FreeDeltaRing σ) * x = (p : FreeDeltaRing σ) * y at hxy
  exact mul_left_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero) hxy

/-- 生成元上で定めたφはmod pでFrobeniusとなる。
多項式環の準同型の外延性で整数係数と各変数を比較する。 -/
theorem freeDeltaFrobenius_mod_p (x : FreeDeltaRing σ) :
    Ideal.Quotient.mk (Ideal.span {(p : FreeDeltaRing σ)}) (freeDeltaFrobenius p σ x) =
      Ideal.Quotient.mk (Ideal.span {(p : FreeDeltaRing σ)}) x ^ p := by
  let I := Ideal.span {(p : FreeDeltaRing σ)}
  let q := Ideal.Quotient.mk I
  have hpu : ¬ IsUnit (p : FreeDeltaRing σ) := by
    intro h
    have hm := h.map (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p))
      (fun _ : σ × ℕ ↦ 0))
    exact zero_ne_one (by
      simpa only [map_natCast, CharP.cast_eq_zero, isUnit_zero_iff] using hm)
  let : CharP (FreeDeltaRing σ ⧸ I) p := CharP.quotient (FreeDeltaRing σ) p hpu
  have hqp : q (p : FreeDeltaRing σ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have h : q.comp (freeDeltaFrobenius p σ) = (frobenius (FreeDeltaRing σ ⧸ I) p).comp q := by
    apply MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
    intro v
    rcases v with ⟨s, n⟩
    simp only [RingHom.comp_apply, freeDeltaFrobenius_X, map_add, map_mul, map_pow,
      hqp, zero_mul, add_zero, frobenius_def]
  exact DFunLike.congr_fun h x

/-- 自由整数δ環のδ構造の存在・一意性。
p正則性とmod p Frobeniusの計算から前段の復元定理を適用する。 -/
theorem existsUnique_freeDeltaStructure :
    ∃! D : DeltaStructure p (FreeDeltaRing σ), D.frobeniusLift = freeDeltaFrobenius p σ :=
  DeltaStructure.existsUnique_of_mod_p (freeDeltaRing_p_mul_injective p σ)
    (freeDeltaFrobenius p σ) (freeDeltaFrobenius_mod_p p σ)

/-- 自由整数δ環の標準δ構造。指定したFrobeniusを持つ一意な構造として選ぶ。 -/
def freeDeltaStructure : DeltaStructure p (FreeDeltaRing σ) :=
  (existsUnique_freeDeltaStructure p σ).choose

/-- 自由整数δ環のFrobenius持上げは、生成元上で指定したφ。 -/
@[simp] theorem freeDeltaStructure_frobeniusLift :
    (freeDeltaStructure p σ).frobeniusLift = freeDeltaFrobenius p σ :=
  (existsUnique_freeDeltaStructure p σ).choose_spec.1

/-- δ(x_(s,n))=x_(s,n+1)。Frobeniusの式からpを消去する。 -/
@[simp] theorem freeDeltaStructure_delta_X (s : σ) (n : ℕ) :
    (freeDeltaStructure p σ).delta (MvPolynomial.X (s, n)) = MvPolynomial.X (s, n + 1) := by
  apply freeDeltaRing_p_mul_injective p σ
  apply add_left_cancel (a := MvPolynomial.X (s, n) ^ p)
  rw [← DeltaStructure.frobeniusLift_apply, freeDeltaStructure_frobeniusLift,
    freeDeltaFrobenius_X]

end SerrePositivity.BhattScholze
