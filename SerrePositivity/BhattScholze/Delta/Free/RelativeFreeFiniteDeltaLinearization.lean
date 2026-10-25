module

public import SerrePositivity.BhattScholze.Delta.Free.PolynomialRankOneDelta
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDeltaResidue
public import Mathlib.Algebra.MvPolynomial.Derivation

/-! # 有限δ計算とrank 1変数の補助δ計算の差

pを消す通常射の下で差は加法的で、Frobeniusを係数作用とするLeibniz公式を満たす。
-/

@[expose] public noncomputable section
universe u v w
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- 同じ有限初期変数をrank 1とした補助δ像を次の段へ含める。 -/
def relativeFreeFiniteRankOneStep (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : MvPolynomial (σ × Fin (N + 2)) A :=
  relativeFreeFiniteStepInclusion N σ
    ((polynomialRankOneDeltaStructure (σ × Fin (N + 1)) D).delta f)

/-- 補助δ計算は係数上で実際の有限δ計算に一致する。 -/
@[simp] theorem relativeFreeFiniteRankOneStep_C (D : DeltaStructure p A) (a : A) :
    relativeFreeFiniteRankOneStep N σ D (MvPolynomial.C a) = MvPolynomial.C (D.delta a) := by
  simp [relativeFreeFiniteRankOneStep, relativeFreeFiniteStepInclusion]

/-- 補助δ計算は変数上で零。 -/
@[simp] theorem relativeFreeFiniteRankOneStep_X (D : DeltaStructure p A)
    (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteRankOneStep N σ D (MvPolynomial.X (s, i)) = 0 := by
  simp [relativeFreeFiniteRankOneStep]

/-- 補助δ計算の加法補正項は、実際の有限δ計算と同じ。 -/
theorem relativeFreeFiniteRankOneStep_add (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteRankOneStep N σ D (f + g) =
      relativeFreeFiniteRankOneStep N σ D f + relativeFreeFiniteRankOneStep N σ D g +
        (WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
          WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ g)).coeff 1 := by
  simp only [relativeFreeFiniteRankOneStep, DeltaStructure.delta_add, map_add]
  rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]

/-- 補助δ計算の積公式。 -/
theorem relativeFreeFiniteRankOneStep_mul (D : DeltaStructure p A)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteRankOneStep N σ D (f * g) =
      (relativeFreeFiniteStepInclusion N σ f) ^ p * relativeFreeFiniteRankOneStep N σ D g +
        relativeFreeFiniteRankOneStep N σ D f * (relativeFreeFiniteStepInclusion N σ g) ^ p +
        (p : MvPolynomial (σ × Fin (N + 2)) A) *
          relativeFreeFiniteRankOneStep N σ D f * relativeFreeFiniteRankOneStep N σ D g := by
  simp only [relativeFreeFiniteRankOneStep, DeltaStructure.delta_mul,
    map_add, map_mul, map_pow, map_natCast]

/-- 通常射の下で比較する、実際の有限δ像と補助δ像の差。 -/
def relativeFreeFiniteDeltaDifference (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f : MvPolynomial (σ × Fin (N + 1)) A) : B :=
  q (relativeFreeFiniteDeltaStep N σ D f) - q (relativeFreeFiniteRankOneStep N σ D f)

/-- 差は基底係数上で零。 -/
@[simp] theorem relativeFreeFiniteDeltaDifference_C (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (a : A) :
    relativeFreeFiniteDeltaDifference N σ D q (MvPolynomial.C a) = 0 := by
  simp [relativeFreeFiniteDeltaDifference]

/-- 差の変数上の値は次のδ変数の通常射による像。 -/
@[simp] theorem relativeFreeFiniteDeltaDifference_X (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B) (s : σ) (i : Fin (N + 1)) :
    relativeFreeFiniteDeltaDifference N σ D q (MvPolynomial.X (s, i)) =
      q (MvPolynomial.X (s, i.succ)) := by
  simp [relativeFreeFiniteDeltaDifference]

/-- 有限δ計算の差は加法的。補正項は両計算で相殺する。 -/
theorem relativeFreeFiniteDeltaDifference_add (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaDifference N σ D q (f + g) =
      relativeFreeFiniteDeltaDifference N σ D q f +
        relativeFreeFiniteDeltaDifference N σ D q g := by
  simp only [relativeFreeFiniteDeltaDifference, relativeFreeFiniteDeltaStep_add,
    relativeFreeFiniteRankOneStep_add, map_add]
  ring

/-- pを消す通常射の下では、差はFrobenius係数のLeibniz公式を満たす。 -/
theorem relativeFreeFiniteDeltaDifference_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaDifference N σ D q (f * g) =
      (q (relativeFreeFiniteStepInclusion N σ f)) ^ p *
        relativeFreeFiniteDeltaDifference N σ D q g +
        relativeFreeFiniteDeltaDifference N σ D q f *
          (q (relativeFreeFiniteStepInclusion N σ g)) ^ p := by
  simp only [relativeFreeFiniteDeltaDifference, relativeFreeFiniteDeltaStep_mul,
    relativeFreeFiniteRankOneStep_mul, map_add, map_mul, map_pow, hp, zero_mul, add_zero]
  ring

/-- 有限δ計算の差を、有限Frobeniusの係数作用についての既存derivationにする。 -/
def relativeFreeFiniteDeltaDifferenceDerivation (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) :
    let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
    letI := φ.toAlgebra
    letI := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
    Derivation A (MvPolynomial (σ × Fin (N + 1)) A) B := by
  let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
  letI := φ.toAlgebra
  letI := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
  exact {
    toFun := relativeFreeFiniteDeltaDifference N σ D q
    map_add' := relativeFreeFiniteDeltaDifference_add N σ D q
    map_smul' := by
      intro r f
      rw [Algebra.smul_def]
      change relativeFreeFiniteDeltaDifference N σ D q (MvPolynomial.C r * f) =
        q (relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.C r)) *
          relativeFreeFiniteDeltaDifference N σ D q f
      rw [relativeFreeFiniteDeltaDifference_mul N σ D q hp,
        relativeFreeFiniteDeltaDifference_C, zero_mul, add_zero,
        relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp]
    map_one_eq_zero' := by
      change relativeFreeFiniteDeltaDifference N σ D q 1 = 0
      simpa only [map_one] using relativeFreeFiniteDeltaDifference_C N σ D q (1 : A)
    leibniz' := by
      intro f g
      change relativeFreeFiniteDeltaDifference N σ D q (f * g) =
        q (relativeFreeFiniteFrobeniusStep N σ D f) * relativeFreeFiniteDeltaDifference N σ D q g +
          q (relativeFreeFiniteFrobeniusStep N σ D g) * relativeFreeFiniteDeltaDifference N σ D q f
      rw [relativeFreeFiniteDeltaDifference_mul N σ D q hp,
        relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp,
        relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp]
      ring }

/-- 構成したderivationの値は、具体的な二つのδ計算の差。 -/
theorem relativeFreeFiniteDeltaDifferenceDerivation_apply (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaDifferenceDerivation N σ D q hp f =
      relativeFreeFiniteDeltaDifference N σ D q f := rfl

/-- 有限δ計算の差は、各次変数の値で指定した既存多項式derivationに一致する。 -/
theorem relativeFreeFiniteDeltaDifference_eq_mkDerivation (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
    letI := φ.toAlgebra
    letI := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
    letI : IsScalarTower A (MvPolynomial (σ × Fin (N + 1)) A) B :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    relativeFreeFiniteDeltaDifference N σ D q f =
      MvPolynomial.mkDerivation A (fun z : σ × Fin (N + 1) =>
        q (MvPolynomial.X (z.1, z.2.succ))) f := by
  let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
  let := φ.toAlgebra
  let := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
  let : IsScalarTower A (MvPolynomial (σ × Fin (N + 1)) A) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have he : relativeFreeFiniteDeltaDifferenceDerivation N σ D q hp =
      MvPolynomial.mkDerivation A (fun z : σ × Fin (N + 1) =>
        q (MvPolynomial.X (z.1, z.2.succ))) := by
    apply MvPolynomial.derivation_ext
    intro z
    obtain ⟨s, i⟩ := z
    rw [relativeFreeFiniteDeltaDifferenceDerivation_apply, relativeFreeFiniteDeltaDifference_X,
      MvPolynomial.mkDerivation_X]
  rw [← relativeFreeFiniteDeltaDifferenceDerivation_apply N σ D q hp, he]

/-- 単項式の有限δ差は、次変数の像の明示的な線形結合。
係数は元の有限多項式のFrobenius像だけを使う。 -/
theorem relativeFreeFiniteDeltaDifference_monomial (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (s : (σ × Fin (N + 1)) →₀ ℕ) (r : A) :
    relativeFreeFiniteDeltaDifference N σ D q (MvPolynomial.monomial s r) =
      q (relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.C r)) *
        s.sum (fun z k => q (relativeFreeFiniteFrobeniusStep N σ D
          (MvPolynomial.monomial (s - Finsupp.single z 1) (k : A))) *
            q (MvPolynomial.X (z.1, z.2.succ))) := by
  let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
  let := φ.toAlgebra
  let := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
  let : IsScalarTower A (MvPolynomial (σ × Fin (N + 1)) A) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have he := relativeFreeFiniteDeltaDifference_eq_mkDerivation N σ D q hp
    (MvPolynomial.monomial s r)
  dsimp only at he
  rw [MvPolynomial.mkDerivation_monomial] at he
  exact he

/-- 任意有限初期多項式のδ差は、次変数の像の明示的な有限線形結合。 -/
theorem relativeFreeFiniteDeltaDifference_polynomial (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaDifference N σ D q f =
      ∑ s ∈ f.support, q (relativeFreeFiniteFrobeniusStep N σ D (MvPolynomial.C (f.coeff s))) *
        s.sum (fun z k => q (relativeFreeFiniteFrobeniusStep N σ D
          (MvPolynomial.monomial (s - Finsupp.single z 1) (k : A))) *
            q (MvPolynomial.X (z.1, z.2.succ))) := by
  classical
  let φ := q.comp (relativeFreeFiniteFrobeniusStep N σ D)
  let := φ.toAlgebra
  let := (φ.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A)).toAlgebra
  rw [← relativeFreeFiniteDeltaDifferenceDerivation_apply N σ D q hp]
  conv_lhs => rw [MvPolynomial.as_sum f]
  change (relativeFreeFiniteDeltaDifferenceDerivation N σ D q hp).toLinearMap
    (∑ s ∈ f.support, MvPolynomial.monomial s (f.coeff s)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change relativeFreeFiniteDeltaDifferenceDerivation N σ D q hp
    (MvPolynomial.monomial s (f.coeff s)) = _
  rw [relativeFreeFiniteDeltaDifferenceDerivation_apply,
    relativeFreeFiniteDeltaDifference_monomial N σ D q hp]

/-- p剰余での有限δ差の係数は、初期変数だけを使う標準包含像のp乗。
新しい次変数は、この有限線形結合の値としてのみ現れる。 -/
theorem relativeFreeFiniteDeltaDifference_polynomial_old_coefficients (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaDifference N σ D q f =
      ∑ s ∈ f.support, (q (relativeFreeFiniteStepInclusion N σ (MvPolynomial.C (f.coeff s)))) ^ p *
        s.sum (fun z k => (q (relativeFreeFiniteStepInclusion N σ
          (MvPolynomial.monomial (s - Finsupp.single z 1) (k : A)))) ^ p *
            q (MvPolynomial.X (z.1, z.2.succ))) := by
  rw [relativeFreeFiniteDeltaDifference_polynomial N σ D q hp]
  simp only [relativeFreeFiniteFrobeniusStep_map_of_prime_zero N σ D q hp]

end SerrePositivity.BhattScholze
