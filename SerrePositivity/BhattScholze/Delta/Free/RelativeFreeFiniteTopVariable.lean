module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteResidue
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# 有限段の δ 像の最高段変数についての解析

## 概要
p 剰余での最高段変数に関する次数、最高係数（基底 Frobenius で表される）、最高偏微分。
BS 著者版 Remark 2.14 の相対自由 δ 座標について、最高段の変数を分離する。

## 方針
最高段変数を分離し、係数側だけを p で割る環射で計算する。

## 規約
係数商に δ 構造を仮定しない。

## 使われ方
d で割る包の関係式が最高変数について一次で係数 φⁿ(d) であることの計算（Division/Relations）。
-/

@[expose] public noncomputable section
universe u v w

/-! ## 有限δ像の最高変数に関するp剰余次数評価

最高変数を分離し、係数側だけをpで割る具体的な環射を使う。
係数商にδ構造を仮定しない。
-/

section RelativeFreeFiniteDeltaTopDegree

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限変数の多項式環のp商。零環も許す。 -/
abbrev RelativeFreeFiniteOldResidue :=
  MvPolynomial (σ × Fin (N + 1)) A ⧸ Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)}

/-- 最高変数を外側へ分離して係数をpで割る標準射。 -/
def relativeFreeFiniteTopResidueMap :
    MvPolynomial (σ × Fin (N + 2)) A →+*
      MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ) :=
  (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)}))).comp
    (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A).toRingHom

/-- 初期多項式の包含像はp商の係数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_inclusion
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteStepInclusion N σ f) =
      MvPolynomial.C (Ideal.Quotient.mk _ f) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_inclusion, MvPolynomial.map_C]

/-- 標準射はpを消す。 -/
theorem relativeFreeFiniteTopResidueMap_prime :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
      (p : MvPolynomial (σ × Fin (N + 2)) A) = 0 := by
  rw [show (p : MvPolynomial (σ × Fin (N + 2)) A) =
    relativeFreeFiniteStepInclusion N σ (p : MvPolynomial (σ × Fin (N + 1)) A) from
      (map_natCast (relativeFreeFiniteStepInclusion N σ) p).symm,
    relativeFreeFiniteTopResidueMap_inclusion]
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self (p : MvPolynomial (σ × Fin (N + 1)) A))
  rw [h, MvPolynomial.C_0]

/-- 最高変数の像は外側の変数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_X_top (s : σ) :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ (MvPolynomial.X (s, Fin.last (N + 1))) =
      MvPolynomial.X s := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_top, MvPolynomial.map_X]

/-- 初期変数の像は係数側の変数。 -/
@[simp] theorem relativeFreeFiniteTopResidueMap_X_initial (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ (MvPolynomial.X (s, i.castSucc)) =
      MvPolynomial.C (Ideal.Quotient.mk _ (MvPolynomial.X (s, i))) := by
  change MvPolynomial.map _ (relativeFreeFiniteTopVariableSplitAlgEquiv N σ A _) = _
  rw [relativeFreeFiniteTopVariableSplitAlgEquiv_X_initial, MvPolynomial.map_C]

/-- 初期多項式の包含像の任意冪は、最高変数に関して次数0。 -/
theorem relativeFreeFiniteTopResidueMap_inclusion_pow_degree
    (f : MvPolynomial (σ × Fin (N + 1)) A) (m : ℕ) :
    ((relativeFreeFiniteTopResidueMap (p := p) N σ
      (relativeFreeFiniteStepInclusion N σ f)) ^ m).totalDegree = 0 := by
  rw [relativeFreeFiniteTopResidueMap_inclusion, ← map_pow, MvPolynomial.totalDegree_C]

/-- 次変数の像は最高変数について次数1以下。係数商が零環でも成立する。 -/
theorem relativeFreeFiniteTopResidueMap_X_succ_degree (s : σ) (i : Fin (N + 1)) :
    (relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
      (MvPolynomial.X (s, i.succ))).totalDegree ≤ 1 := by
  by_cases hi : i.val < N
  · let j : Fin (N + 1) := ⟨i.val + 1, by omega⟩
    have he : i.succ = j.castSucc := Fin.ext rfl
    rw [he, relativeFreeFiniteTopResidueMap_X_initial, MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1
  · have he : i.succ = Fin.last (N + 1) := by
      apply Fin.ext
      have hn := i.isLt
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [he, relativeFreeFiniteTopResidueMap_X_top]
    rcases subsingleton_or_nontrivial
      (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ) with h | h
    · let := h
      have hz : (MvPolynomial.X s :
          MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ)) = 0 :=
        Subsingleton.elim _ _
      rw [hz, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le 1
    · let := h
      rw [MvPolynomial.totalDegree_X]

variable [Fact p.Prime]

/-- rank 1補助δ計算の像は初期係数だけを使う。 -/
theorem relativeFreeFiniteTopResidueMap_rankOneStep (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteRankOneStep N σ D f) =
      MvPolynomial.C (Ideal.Quotient.mk _
        ((polynomialRankOneDeltaStructure (σ × Fin (N + 1)) D).delta f)) :=
  relativeFreeFiniteTopResidueMap_inclusion N σ _

/-- p剰余で有限δ差の最高変数全体の次数は1以下。 -/
theorem relativeFreeFiniteDeltaDifference_top_degree (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteDeltaDifference N σ D
      (relativeFreeFiniteTopResidueMap (p := p) N σ) f).totalDegree ≤ 1 := by
  classical
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  rw [relativeFreeFiniteDeltaDifference_polynomial_old_coefficients N σ D q
    (relativeFreeFiniteTopResidueMap_prime N σ)]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hinner : (s.sum (fun z k => (q (relativeFreeFiniteStepInclusion N σ
      (MvPolynomial.monomial (s - Finsupp.single z 1) (k : A)))) ^ p *
        q (MvPolynomial.X (z.1, z.2.succ)))).totalDegree ≤ 1 := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro z hz
    apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [relativeFreeFiniteTopResidueMap_inclusion_pow_degree, zero_add]
    exact relativeFreeFiniteTopResidueMap_X_succ_degree N σ z.1 z.2
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [relativeFreeFiniteTopResidueMap_inclusion_pow_degree, zero_add]
  exact hinner

/-- 任意有限δ像のp剰余は、最高変数全体に関して次数1以下。 -/
theorem relativeFreeFiniteDeltaStep_top_degree (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteTopResidueMap (p := p) N σ
      (relativeFreeFiniteDeltaStep N σ D f)).totalDegree ≤ 1 := by
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he : q (relativeFreeFiniteDeltaStep N σ D f) =
      relativeFreeFiniteDeltaDifference N σ D q f + q (relativeFreeFiniteRankOneStep N σ D f) := by
    exact (sub_add_cancel _ _).symm
  rw [he, relativeFreeFiniteTopResidueMap_rankOneStep]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · exact relativeFreeFiniteDeltaDifference_top_degree N σ D f
  · rw [MvPolynomial.totalDegree_C]
    exact Nat.zero_le 1

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaTopDegree

/-! ## 有限δ像の最高変数係数

初期係数p商へのFrobenius射を明示し、最高変数の係数を偏微分で計算する。
-/

section RelativeFreeFiniteDeltaTopCoefficient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限環の補助Frobeniusとp商の合成。零係数商も含む。 -/
def relativeFreeFiniteOldFrobenius (D : DeltaStructure p A) :
    MvPolynomial (σ × Fin (N + 1)) A →+* RelativeFreeFiniteOldResidue (p := p) (A := A) N σ :=
  (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)})).comp
    (polynomialRankOneDeltaStructure (σ × Fin (N + 1)) D).frobeniusLift

/-- 初期Frobeniusのp商像は標準商像のp乗。 -/
theorem relativeFreeFiniteOldFrobenius_apply (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteOldFrobenius N σ D f = (Ideal.Quotient.mk _ f) ^ p := by
  have hp := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self (p : MvPolynomial (σ × Fin (N + 1)) A))
  simp only [relativeFreeFiniteOldFrobenius, RingHom.comp_apply, DeltaStructure.frobeniusLift_apply,
    map_add, map_pow, map_mul, hp, zero_mul, add_zero]

/-- 最高変数分離後の有限Frobenius像は初期Frobeniusの係数像。 -/
theorem relativeFreeFiniteTopResidueMap_frobenius (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteFrobeniusStep N σ D f) =
      MvPolynomial.C (relativeFreeFiniteOldFrobenius N σ D f) := by
  rw [relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D _
    (relativeFreeFiniteTopResidueMap_prime N σ), relativeFreeFiniteTopResidueMap_inclusion,
    ← map_pow, relativeFreeFiniteOldFrobenius_apply]

/-- 実際の有限δ像の外側最高変数X_sの係数。 -/
def relativeFreeFiniteDeltaTopCoefficient (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : RelativeFreeFiniteOldResidue (p := p) (A := A) N σ :=
  (relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteDeltaStep N σ D f)).coeff
    (Finsupp.single s 1)

/-- 補助rank 1δ像は最高変数の係数へ寄与しない。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_difference (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s f =
      (relativeFreeFiniteDeltaDifference N σ D
        (relativeFreeFiniteTopResidueMap (p := p) N σ) f).coeff (Finsupp.single s 1) := by
  classical
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he : q (relativeFreeFiniteDeltaStep N σ D f) =
      relativeFreeFiniteDeltaDifference N σ D q f + q (relativeFreeFiniteRankOneStep N σ D f) :=
    (sub_add_cancel _ _).symm
  unfold relativeFreeFiniteDeltaTopCoefficient
  rw [he, relativeFreeFiniteTopResidueMap_rankOneStep,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    MvPolynomial.coeff_C_of_ne_zero (by simp), add_zero]

/-- 最高変数の係数は加法的。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_add (D : DeltaStructure p A) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (f + g) =
      relativeFreeFiniteDeltaTopCoefficient N σ D s f +
        relativeFreeFiniteDeltaTopCoefficient N σ D s g := by
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_difference,
    relativeFreeFiniteDeltaDifference_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    ← relativeFreeFiniteDeltaTopCoefficient_eq_difference,
    ← relativeFreeFiniteDeltaTopCoefficient_eq_difference]

/-- 最高変数係数のFrobenius係数Leibniz公式。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_mul (D : DeltaStructure p A) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (f * g) =
      relativeFreeFiniteOldFrobenius N σ D f * relativeFreeFiniteDeltaTopCoefficient N σ D s g +
        relativeFreeFiniteDeltaTopCoefficient N σ D s f *
          relativeFreeFiniteOldFrobenius N σ D g := by
  let q := relativeFreeFiniteTopResidueMap (p := p) (A := A) N σ
  have he := relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q
    (relativeFreeFiniteTopResidueMap_prime N σ) f g
  rw [relativeFreeFiniteTopResidueMap_inclusion, relativeFreeFiniteTopResidueMap_inclusion] at he
  simp only [← map_pow (MvPolynomial.C : RelativeFreeFiniteOldResidue (p := p) (A := A) N σ →+*
    MvPolynomial σ (RelativeFreeFiniteOldResidue (p := p) (A := A) N σ))] at he
  rw [← relativeFreeFiniteOldFrobenius_apply N σ D f,
    ← relativeFreeFiniteOldFrobenius_apply N σ D g] at he
  have hcoeff := congrArg (fun z => z.coeff (Finsupp.single s 1)) he
  rw [mul_comm (q (relativeFreeFiniteDeltaStep N σ D f))
    (MvPolynomial.C (relativeFreeFiniteOldFrobenius N σ D g))] at hcoeff
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_C_mul] at hcoeff
  change relativeFreeFiniteDeltaTopCoefficient N σ D s (f * g) =
    relativeFreeFiniteOldFrobenius N σ D f * relativeFreeFiniteDeltaTopCoefficient N σ D s g +
      relativeFreeFiniteOldFrobenius N σ D g *
        relativeFreeFiniteDeltaTopCoefficient N σ D s f at hcoeff
  rw [mul_comm (relativeFreeFiniteOldFrobenius N σ D g)
    (relativeFreeFiniteDeltaTopCoefficient N σ D s f)] at hcoeff
  exact hcoeff

/-- 基底係数のδ像は外側最高変数の係数に寄与しない。 -/
@[simp] theorem relativeFreeFiniteDeltaTopCoefficient_C (D : DeltaStructure p A) (s : σ) (a : A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (MvPolynomial.C a) = 0 := by
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_difference, relativeFreeFiniteDeltaDifference_C]
  simp

/-- 各有限変数の最高係数は、最高段の対応する変数だけを検出する。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_X (D : DeltaStructure p A) (s t : σ)
    (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s (MvPolynomial.X (t, i)) =
      relativeFreeFiniteOldFrobenius N σ D
        (MvPolynomial.pderiv (s, Fin.last N) (MvPolynomial.X (t, i))) := by
  classical
  unfold relativeFreeFiniteDeltaTopCoefficient
  rw [relativeFreeFiniteDeltaStep_X]
  by_cases hi : i = Fin.last N
  · subst i
    change (relativeFreeFiniteTopResidueMap (p := p) N σ
      (MvPolynomial.X (t, Fin.last (N + 1)))).coeff (Finsupp.single s 1) = _
    rw [relativeFreeFiniteTopResidueMap_X_top]
    by_cases ht : t = s
    · subst t
      simp [MvPolynomial.pderiv_X, MvPolynomial.coeff_X]
    · simp [MvPolynomial.pderiv_X, MvPolynomial.coeff_X, ht,
        Finsupp.single_eq_single_iff]
  · have hn : i.val < N := by
      have hb := i.isLt
      by_contra h
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    let j : Fin (N + 1) := ⟨i.val + 1, by omega⟩
    have he : i.succ = j.castSucc := Fin.ext rfl
    rw [he, relativeFreeFiniteTopResidueMap_X_initial,
      MvPolynomial.coeff_C_of_ne_zero (by simp)]
    have hj : (t, i) ≠ (s, Fin.last N) := fun h => hi (congrArg Prod.snd h)
    rw [MvPolynomial.pderiv_X_of_ne hj, map_zero]

/-- 任意有限δ像の最高係数は、初期偏微分のFrobenius商像。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_frobenius_pderiv (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopCoefficient N σ D s f =
      relativeFreeFiniteOldFrobenius N σ D (MvPolynomial.pderiv (s, Fin.last N) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
      rw [relativeFreeFiniteDeltaTopCoefficient_add, map_add, map_add, hf, hg]
  | mul_X f z hf =>
      obtain ⟨t, i⟩ := z
      rw [relativeFreeFiniteDeltaTopCoefficient_mul, MvPolynomial.pderiv_mul, map_add,
        map_mul, map_mul, relativeFreeFiniteDeltaTopCoefficient_X, hf]
      ring

/-- 最高変数係数は、初期偏微分のp商像のp乗。零係数商も含む。 -/
theorem relativeFreeFiniteDeltaTopCoefficient_eq_pderiv_pow (D : DeltaStructure p A) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (relativeFreeFiniteTopResidueMap (p := p) N σ (relativeFreeFiniteDeltaStep N σ D f)).coeff
      (Finsupp.single s 1) =
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial (σ × Fin (N + 1)) A)})
        (MvPolynomial.pderiv (s, Fin.last N) f)) ^ p := by
  change relativeFreeFiniteDeltaTopCoefficient N σ D s f = _
  rw [relativeFreeFiniteDeltaTopCoefficient_eq_frobenius_pderiv,
    relativeFreeFiniteOldFrobenius_apply]

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaTopCoefficient

/-! ## 任意通常p剰余での有限δ像の最高偏微分

初期包含の最高偏微分が零であることから、実際のδ計算を微分する。
-/

section RelativeFreeFiniteDeltaTopDerivative

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- 初期包含多項式には次段の最高変数が現れず、その偏微分は零。 -/
theorem relativeFreeFiniteStepInclusion_top_pderiv_zero (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteStepInclusion N σ f) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  change (s, Fin.last (N + 1)) ∈
    (MvPolynomial.rename (fun z : σ × Fin (N + 1) => (z.1, z.2.castSucc)) f).vars at h
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ h
  have hi := i.isLt
  have hv := congrArg (fun z : σ × Fin (N + 2) => z.2.val) he
  simp only [Fin.val_castSucc, Fin.val_last] at hv
  omega

/-- 有限δ加法補正項は初期補正項の標準包含の像。 -/
theorem relativeFreeFiniteStepInclusion_additionCarry
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    (WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
      WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ g)).coeff 1 =
      relativeFreeFiniteStepInclusion N σ
        ((WittVector.teichmuller p f + WittVector.teichmuller p g).coeff 1) := by
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]

/-- 通常射の下で有限δ像の最高偏微分を取り出す。 -/
def relativeFreeFiniteDeltaTopDerivative (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : B :=
  q (MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteDeltaStep N σ D f))

/-- 最高偏微分の像は加法的。 -/
theorem relativeFreeFiniteDeltaTopDerivative_add (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (f + g) =
      relativeFreeFiniteDeltaTopDerivative N σ D q s f +
        relativeFreeFiniteDeltaTopDerivative N σ D q s g := by
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_add, relativeFreeFiniteStepInclusion_additionCarry,
    map_add, map_add, relativeFreeFiniteStepInclusion_top_pderiv_zero,
    map_add, map_add, map_zero, add_zero]

/-- pを消す通常射の下での最高偏微分のFrobenius係数Leibniz公式。 -/
theorem relativeFreeFiniteDeltaTopDerivative_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) (s : σ)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (f * g) =
      q (relativeFreeFiniteFrobeniusStep N σ D f) *
        relativeFreeFiniteDeltaTopDerivative N σ D q s g +
        relativeFreeFiniteDeltaTopDerivative N σ D q s f *
          q (relativeFreeFiniteFrobeniusStep N σ D g) := by
  have hf : MvPolynomial.pderiv (s, Fin.last (N + 1))
      ((relativeFreeFiniteStepInclusion N σ f) ^ p) = 0 := by
    rw [MvPolynomial.pderiv_pow, relativeFreeFiniteStepInclusion_top_pderiv_zero, mul_zero]
  have hg : MvPolynomial.pderiv (s, Fin.last (N + 1))
      ((relativeFreeFiniteStepInclusion N σ g) ^ p) = 0 := by
    rw [MvPolynomial.pderiv_pow, relativeFreeFiniteStepInclusion_top_pderiv_zero, mul_zero]
  have hprime : MvPolynomial.pderiv (s, Fin.last (N + 1))
      (p : MvPolynomial (σ × Fin (N + 2)) A) = 0 := by
    rw [show (p : MvPolynomial (σ × Fin (N + 2)) A) = MvPolynomial.C (p : A) from
      (map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 2)) A) p).symm,
      MvPolynomial.pderiv_C]
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_mul]
  simp only [map_add, MvPolynomial.pderiv_mul, hf, hg, hprime, zero_mul, mul_zero,
    zero_add, add_zero, map_mul, map_pow, hp]
  rw [relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp,
    relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp]

/-- 係数の有限δ像の最高偏微分は零。 -/
@[simp] theorem relativeFreeFiniteDeltaTopDerivative_C (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ) (a : A) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (MvPolynomial.C a) = 0 := by
  simp [relativeFreeFiniteDeltaTopDerivative]

/-- 各変数の最高偏微分の像は初期偏微分の有限Frobenius像。 -/
theorem relativeFreeFiniteDeltaTopDerivative_X (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s t : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaTopDerivative N σ D q s (MvPolynomial.X (t, i)) =
      q (relativeFreeFiniteFrobeniusStep N σ D
        (MvPolynomial.pderiv (s, Fin.last N) (MvPolynomial.X (t, i)))) := by
  classical
  unfold relativeFreeFiniteDeltaTopDerivative
  rw [relativeFreeFiniteDeltaStep_X]
  by_cases hi : i = Fin.last N
  · subst i
    change q (MvPolynomial.pderiv (s, Fin.last (N + 1))
      (MvPolynomial.X (t, Fin.last (N + 1)))) = _
    by_cases ht : t = s
    · subst t
      simp [MvPolynomial.pderiv_X]
    · simp [MvPolynomial.pderiv_X, ht, (Fact.out : p.Prime).ne_zero]
  · have hj : (t, i.succ) ≠ (s, Fin.last (N + 1)) := by
      intro h
      apply hi
      apply Fin.ext
      have hv := congrArg (fun z : σ × Fin (N + 2) => z.2.val) h
      simp only [Fin.val_succ, Fin.val_last] at hv
      simp only [Fin.val_last]
      omega
    have hj' : (t, i) ≠ (s, Fin.last N) := fun h => hi (congrArg Prod.snd h)
    rw [MvPolynomial.pderiv_X_of_ne hj, map_zero,
      MvPolynomial.pderiv_X_of_ne hj', map_zero, map_zero]

/-- 有限Frobenius射は基底係数上で基底Frobeniusに一致する。 -/
@[simp] theorem relativeFreeFiniteFrobeniusStep_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.C a) =
      MvPolynomial.C (D.frobeniusLift a) := by
  simp [relativeFreeFiniteFrobeniusStep_apply, relativeFreeFiniteStepInclusion,
    DeltaStructure.frobeniusLift_apply]

/-- 任意通常p剰余で、最高偏微分は初期偏微分の有限Frobenius像。 -/
theorem relativeFreeFiniteDeltaTopDerivative_eq_frobenius_pderiv (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) (s : σ)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (MvPolynomial.pderiv (s, Fin.last (N + 1)) (relativeFreeFiniteDeltaStep N σ D f)) =
      q (relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.pderiv (s, Fin.last N) f)) := by
  change relativeFreeFiniteDeltaTopDerivative N σ D q s f = _
  induction f using MvPolynomial.induction_on with
  | C a => simp [(Fact.out : p.Prime).ne_zero]
  | add f g hf hg =>
      rw [relativeFreeFiniteDeltaTopDerivative_add, map_add, map_add, map_add, hf, hg]
  | mul_X f z hf =>
      obtain ⟨t, i⟩ := z
      rw [relativeFreeFiniteDeltaTopDerivative_mul N σ D q hp, MvPolynomial.pderiv_mul,
        map_add, map_add, map_mul, map_mul, map_mul, map_mul,
        relativeFreeFiniteDeltaTopDerivative_X, hf]
      ring

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaTopDerivative
