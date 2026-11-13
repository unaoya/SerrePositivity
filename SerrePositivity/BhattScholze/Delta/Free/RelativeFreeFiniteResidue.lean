module

public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import SerrePositivity.BhattScholze.Delta.Distinguished.Distinguished
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaAdicCompletion
public import Mathlib.Algebra.MvPolynomial.Division
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeFiniteDelta
public import Mathlib.RingTheory.Ideal.Operations
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# p を消す環射の下での δ の計算

## 概要
任意の δ 環で、p を零に送る環射を通した δ の反復・和・積の計算と加法の補正項の積可除性。
その有限段版：剰余公式、p 倍・d 倍の補正、初期包含の核の平方での不変性、rank 1 の補助計算との差（Frobenius を係数とする微分）。
BS 著者版 Remark 2.14 の相対自由 δ 座標について、有限段の剰余を比較する。

## 方針
剰余環に δ 構造を要求せず、源で δ を計算してから環射で送る。

## 規約
剰余環の δ 安定性を仮定しない。

## 使われ方
d で割る包の関係式の (p,d) 剰余の計算（Division/Relations）、André の一段の拡大。
-/

@[expose] public noncomputable section
universe u v w

/-! ## 通常剰余射の下でのδ反復計算

δは剰余環へ降りるとは仮定せず、源でδを計算してから環射で写す。
既存のWitt自然性・δ冪の可除性・δ(p)の合同式を再利用する。
-/

section DeltaResidueArithmetic

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- pを消す任意の通常環射の下で、δ(p)は1となる。零終域も含む。 -/
theorem map_delta_prime_of_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) : q (D.delta (p : A)) = 1 := by
  have hle : Ideal.span {(p : A)} ≤ RingHom.ker q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hp
  have he := hle (D.delta_p_sub_one_mem)
  change q (D.delta (p : A) - 1) = 0 at he
  rw [map_sub, map_one, sub_eq_zero] at he
  exact he

/-- pを消す射の下でδ(x^p)は零。源のp正則性は不要。 -/
theorem map_delta_pow_prime_of_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x : A) : q (D.delta (x ^ p)) = 0 := by
  obtain ⟨b, hb⟩ := D.p_mul_delta_dvd_delta_pow x
  rw [hb, map_mul, map_mul, hp, zero_mul, zero_mul]

/-- 左項が消える通常環射の下では、δの加法補正項も消える。 -/
theorem map_delta_add_of_left_zero (D : DeltaStructure p A) (q : A →+* B)
    (x y : A) (hx : q x = 0) : q (D.delta (x + y)) = q (D.delta x) + q (D.delta y) := by
  exact wittTwoLift_map_delta_add_of_left_zero (RingHom.id A) D.sectionHom D.projection_comp
    q x y hx

/-- 右項が消える場合のδ加法公式。 -/
theorem map_delta_add_of_right_zero (D : DeltaStructure p A) (q : A →+* B)
    (x y : A) (hy : q y = 0) : q (D.delta (x + y)) = q (D.delta x) + q (D.delta y) := by
  exact wittTwoLift_map_delta_add_of_right_zero (RingHom.id A) D.sectionHom D.projection_comp
    q x y hy

/-- pを消す通常環射の下でのδ積公式。 -/
theorem map_delta_mul_of_prime_zero (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) :
    q (D.delta (x * y)) = (q x) ^ p * q (D.delta y) + q (D.delta x) * (q y) ^ p := by
  exact wittTwoLift_map_delta_mul_of_prime_zero (RingHom.id A) D.sectionHom D.projection_comp
    q hp x y

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaResidueArithmetic

/-! ## δ加法補正項の積可除性

整数係数の二変数で補正項を計算し、各変数での消滅から積可除性を得る。
第2有限δ関係式に必要な、通常射の下での補正項のδ像を制御する。
-/

section DeltaAdditionCarryProduct

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- Witt第1加法補正項は二つの入力の積で割り切れる。 -/
theorem wittAdditionCarry_dvd_product (x y : A) :
    x * y ∣ (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
  let U := MvPolynomial Bool ℤ
  let X : U := MvPolynomial.X false
  let Y : U := MvPolynomial.X true
  let c : U := (WittVector.teichmuller p X + WittVector.teichmuller p Y).coeff 1
  have hx : X ∣ c := by
    apply Ideal.mem_span_singleton.mp
    have h := wittAdditionCarry_mem_of_right_mem (p := p) (Ideal.span {X}) Y X
      (Ideal.subset_span (by simp))
    simpa only [add_comm] using h
  have hy : Y ∣ c := by
    apply Ideal.mem_span_singleton.mp
    exact wittAdditionCarry_mem_of_right_mem (p := p) (Ideal.span {Y}) X Y
      (Ideal.subset_span (by simp))
  obtain ⟨z, hz⟩ := hx
  rw [hz] at hy
  have hyz : Y ∣ z := by
    rcases MvPolynomial.X_dvd_mul_iff.mp hy with hYX | hYz
    · have h := MvPolynomial.X_dvd_X.mp hYX
      exact Bool.noConfusion h
    · exact hYz
  obtain ⟨w, hw⟩ := hyz
  have hc : c = (X * Y) * w := by rw [hz, hw, mul_assoc]
  let f : U →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun b => if b then y else x)
  have hfX : f X = x := by
    exact MvPolynomial.eval₂Hom_X' (Int.castRingHom A) (fun b => if b then y else x) false
  have hfY : f Y = y := by
    exact MvPolynomial.eval₂Hom_X' (Int.castRingHom A) (fun b => if b then y else x) true
  have hfc : f c = (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 := by
    change f ((WittVector.teichmuller p X + WittVector.teichmuller p Y).coeff 1) = _
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hfX, hfY]
  refine ⟨f w, ?_⟩
  have he := congrArg f hc
  simpa only [hfc, map_mul, hfX, hfY] using he

/-- 二つの入力がイデアルに属すれば、第1補正項はその平方に属する。 -/
theorem wittAdditionCarry_mem_square (I : Ideal A) (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ I ^ 2 := by
  obtain ⟨z, hz⟩ := wittAdditionCarry_dvd_product (p := p) x y
  rw [hz]
  have hxy : x * y ∈ I ^ 2 := by simpa only [pow_two] using Ideal.mul_mem_mul hx hy
  exact (I ^ 2).mul_mem_right z hxy

/-- pと両入力を消す通常射の下では、第1補正項のδ像も消える。 -/
theorem DeltaStructure.map_delta_additionCarry_of_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hx : q x = 0) (hy : q y = 0) :
    q (D.delta ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1)) = 0 := by
  have hc := wittAdditionCarry_mem_square (p := p) (RingHom.ker q) x y hx hy
  have he := D.delta_mem_pow (RingHom.ker q) hp 1 _ hc
  simpa only [pow_one, RingHom.mem_ker] using he

/-- 第2δの加法公式：両入力と左のδ像が消える場合は補正項も消える。 -/
theorem DeltaStructure.map_delta_delta_add_of_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hx : q x = 0) (hy : q y = 0)
    (hdx : q (D.delta x) = 0) :
    q (D.delta (D.delta (x + y))) = q (D.delta (D.delta x)) + q (D.delta (D.delta y)) := by
  let c := (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1
  have hc : q c = 0 := by
    change q ((WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1) = 0
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller,
      WittVector.map_teichmuller, hx, hy, WittVector.teichmuller_zero, add_zero,
      WittVector.zero_coeff]
  have hdc : q (D.delta c) = 0 := D.map_delta_additionCarry_of_zero q hp x y hx hy
  rw [D.delta_add]
  change q (D.delta (D.delta x + D.delta y + c)) = _
  rw [D.map_delta_add_of_right_zero q (D.delta x + D.delta y) c hc,
    D.map_delta_add_of_left_zero q (D.delta x) (D.delta y) hdx, hdc, add_zero]

/-- 通常射が差とその最初の二つのδ像を消せば、両元のδ²像は一致する。
右元の像が零であることを明示する。商のδ構造は仮定しない。 -/
theorem DeltaStructure.map_delta_delta_eq_of_difference_zero
    {B : Type v} [CommRing B] (D : DeltaStructure p A) (q : A →+* B)
    (hp : q (p : A) = 0) (x y : A) (hy : q y = 0)
    (h0 : q (x - y) = 0) (h1 : q (D.delta (x - y)) = 0)
    (h2 : q (D.delta (D.delta (x - y))) = 0) :
    q (D.delta (D.delta x)) = q (D.delta (D.delta y)) := by
  have he := D.map_delta_delta_add_of_zero q hp (x - y) y h0 hy h1
  simpa only [sub_add_cancel, h2, zero_add] using he

end SerrePositivity.BhattScholze

end DeltaAdditionCarryProduct

/-! ## 有限δ計算の通常剰余公式

次の有限環からの通常射を明示し、pが消える場合の計算を行う。
有限剰余環のδ構造は要求しない。
-/

section RelativeFreeFiniteDeltaResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- pを消す通常射の下で有限Frobenius計算は標準包含のp乗。 -/
theorem relativeFreeFiniteFrobeniusStep_map_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteFrobeniusStep N σ D f) =
      (q (relativeFreeFiniteStepInclusion N σ f)) ^ p := by
  rw [relativeFreeFiniteFrobeniusStep_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]

/-- pを消す通常射の下で有限δ積の第三項は消える。 -/
theorem relativeFreeFiniteDeltaStep_map_mul_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (f * g)) =
      (q (relativeFreeFiniteStepInclusion N σ f)) ^ p * q (relativeFreeFiniteDeltaStep N σ D g) +
        q (relativeFreeFiniteDeltaStep N σ D f) *
          (q (relativeFreeFiniteStepInclusion N σ g)) ^ p := by
  exact wittTwoLift_map_delta_mul_of_prime_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q hp f g

/-- 左入力の包含像が消える通常射では有限δ加法の補正項も消える。 -/
theorem relativeFreeFiniteDeltaStep_map_add_of_left_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) (hf : q (relativeFreeFiniteStepInclusion N σ f) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (f + g)) =
      q (relativeFreeFiniteDeltaStep N σ D f) + q (relativeFreeFiniteDeltaStep N σ D g) := by
  exact wittTwoLift_map_delta_add_of_left_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q f g hf

/-- 右入力の包含像が消える場合の有限δ加法公式。 -/
theorem relativeFreeFiniteDeltaStep_map_add_of_right_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (f g : MvPolynomial (σ × Fin (N + 1)) A) (hg : q (relativeFreeFiniteStepInclusion N σ g) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (f + g)) =
      q (relativeFreeFiniteDeltaStep N σ D f) + q (relativeFreeFiniteDeltaStep N σ D g) := by
  exact wittTwoLift_map_delta_add_of_right_zero (relativeFreeFiniteStepInclusion N σ)
    (relativeFreeFiniteDeltaStepSection N σ D)
    (relativeFreeFiniteDeltaStepSection_projection N σ D) q f g hg

/-- pを消す通常射の下での有限δ計算の正整数冪公式。 -/
theorem relativeFreeFiniteDeltaStep_map_pow_succ_of_prime_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (m : ℕ) :
    q (relativeFreeFiniteDeltaStep N σ D (f ^ (m + 1))) =
      (m + 1 : ℕ) * (q (relativeFreeFiniteStepInclusion N σ f)) ^ (p * m) *
        q (relativeFreeFiniteDeltaStep N σ D f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
        map_pow, map_pow, ih]
      have he : ((q (relativeFreeFiniteStepInclusion N σ f)) ^ (m + 1)) ^ p =
          (q (relativeFreeFiniteStepInclusion N σ f)) ^ (p * m) *
            (q (relativeFreeFiniteStepInclusion N σ f)) ^ p := by
        rw [← pow_mul, Nat.add_mul, Nat.one_mul, Nat.mul_comm m p, pow_add]
      rw [he, Nat.mul_succ, pow_add]
      push_cast
      ring

/-- pを消す通常射の下で、有限δ計算のp乗の像は零。 -/
theorem relativeFreeFiniteDeltaStep_map_pow_prime_of_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (f ^ p)) = 0 := by
  have hpB : (p : B) = 0 := by simpa only [map_natCast] using hp
  have he := relativeFreeFiniteDeltaStep_map_pow_succ_of_prime_zero N σ D q hp f (p - 1)
  rw [Nat.sub_add_cancel (Fact.out : p.Prime).pos] at he
  rw [he, hpB, zero_mul, zero_mul]

/-- pを消す通常射の下で、有限δ計算のδ(p)は1。 -/
theorem relativeFreeFiniteDeltaStep_map_prime_of_zero (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0) :
    q (relativeFreeFiniteDeltaStep N σ D (p : MvPolynomial (σ × Fin (N + 1)) A)) = 1 := by
  have hp' : (q.comp (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 2)) A)) (p : A) = 0 := by
    simpa only [RingHom.comp_apply, map_natCast] using hp
  have he := D.map_delta_prime_of_zero (q.comp MvPolynomial.C) hp'
  rw [show (p : MvPolynomial (σ × Fin (N + 1)) A) = MvPolynomial.C (p : A) from
    (map_natCast (MvPolynomial.C : A →+* MvPolynomial (σ × Fin (N + 1)) A) p).symm,
    relativeFreeFiniteDeltaStep_C]
  exact he

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaResidue

/-! ## 有限δ計算の減算誤差の平方所属

包含像が消えるイデアルの二乗まで、有限δ計算は符号・減算を保つ。
-/

section RelativeFreeFiniteDeltaSubtraction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 有限δ計算の符号の誤差は、入力の包含像を含むイデアルの二乗に属する。 -/
theorem relativeFreeFiniteDeltaStep_neg_error_mem_square (D : DeltaStructure p A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : relativeFreeFiniteStepInclusion N σ f ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (-f) + relativeFreeFiniteDeltaStep N σ D f ∈ I ^ 2 := by
  have hn : relativeFreeFiniteStepInclusion N σ (-f) ∈ I := by
    rw [map_neg]
    exact I.neg_mem hf
  have hc := wittAdditionCarry_mem_square (p := p) I
    (relativeFreeFiniteStepInclusion N σ f) (relativeFreeFiniteStepInclusion N σ (-f)) hf hn
  have he := relativeFreeFiniteDeltaStep_add N σ D f (-f)
  rw [add_neg_cancel, relativeFreeFiniteDeltaStep_zero] at he
  have herr : relativeFreeFiniteDeltaStep N σ D (-f) + relativeFreeFiniteDeltaStep N σ D f =
      -((WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ f) +
        WittVector.teichmuller p (relativeFreeFiniteStepInclusion N σ (-f))).coeff 1) := by
    rw [add_comm (relativeFreeFiniteDeltaStep N σ D (-f))
      (relativeFreeFiniteDeltaStep N σ D f)]
    exact eq_neg_of_add_eq_zero_left he.symm
  rw [herr]
  exact (I ^ 2).neg_mem hc

/-- 二つの包含像が属すイデアルの二乗まで、有限δ計算は減算を保つ。 -/
theorem relativeFreeFiniteDeltaStep_sub_error_mem_square (D : DeltaStructure p A)
    (I : Ideal (MvPolynomial (σ × Fin (N + 2)) A))
    (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : relativeFreeFiniteStepInclusion N σ f ∈ I)
    (hg : relativeFreeFiniteStepInclusion N σ g ∈ I) :
    relativeFreeFiniteDeltaStep N σ D (f - g) -
      (relativeFreeFiniteDeltaStep N σ D f - relativeFreeFiniteDeltaStep N σ D g) ∈ I ^ 2 := by
  have hn : relativeFreeFiniteStepInclusion N σ (-g) ∈ I := by
    rw [map_neg]
    exact I.neg_mem hg
  have hc := wittAdditionCarry_mem_square (p := p) I
    (relativeFreeFiniteStepInclusion N σ f) (relativeFreeFiniteStepInclusion N σ (-g)) hf hn
  have he := (I ^ 2).add_mem
    (relativeFreeFiniteDeltaStep_neg_error_mem_square N σ D I g hg) hc
  rw [sub_eq_add_neg f g, relativeFreeFiniteDeltaStep_add]
  convert he using 1
  ring

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaSubtraction

/-! ## 有限δ計算におけるp倍・d倍の代表元補正

通常射がp,dを消す場合、補正のδ像をp乗の項として明示する。
有限商のδ安定性を仮定しない。
-/

section RelativeFreeFiniteDeltaPerturbation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- p倍の補正は有限δ計算の後、包含像のp乗となる。 -/
theorem relativeFreeFiniteDeltaStep_map_prime_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (g : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D ((p : MvPolynomial (σ × Fin (N + 1)) A) * g)) =
      (q (relativeFreeFiniteStepInclusion N σ g)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
    map_natCast, hp, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul,
    relativeFreeFiniteDeltaStep_map_prime_of_zero N σ D q hp, one_mul, zero_add]

/-- 消える基底係数dの倍は、δ(d)係数付きのp乗となる。 -/
theorem relativeFreeFiniteDeltaStep_map_generator_mul (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (h : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D (MvPolynomial.C d * h)) =
      q (MvPolynomial.C (D.delta d)) *
        (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp]
  have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
    change MvPolynomial.rename _ (MvPolynomial.C d) = _
    exact MvPolynomial.rename_C _ d
  rw [hC, hd, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, zero_add,
    relativeFreeFiniteDeltaStep_C]

/-- p倍・d倍による代表元の変更は、二つの明示的p乗項を加える。 -/
theorem relativeFreeFiniteDeltaStep_map_perturbation (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (f g h : MvPolynomial (σ × Fin (N + 1)) A) :
    q (relativeFreeFiniteDeltaStep N σ D
      (f + (p : MvPolynomial (σ × Fin (N + 1)) A) * g + MvPolynomial.C d * h)) =
      q (relativeFreeFiniteDeltaStep N σ D f) +
        (q (relativeFreeFiniteStepInclusion N σ g)) ^ p +
          q (MvPolynomial.C (D.delta d)) *
            (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  have hpg : q (relativeFreeFiniteStepInclusion N σ
      ((p : MvPolynomial (σ × Fin (N + 1)) A) * g)) = 0 := by
    rw [map_mul, map_mul, map_natCast, hp, zero_mul]
  have hdh : q (relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d * h)) = 0 := by
    rw [map_mul, map_mul]
    have hC : relativeFreeFiniteStepInclusion N σ (MvPolynomial.C d) = MvPolynomial.C d := by
      change MvPolynomial.rename _ (MvPolynomial.C d) = _
      exact MvPolynomial.rename_C _ d
    rw [hC, hd, zero_mul]
  rw [relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q _ _ hdh,
    relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q _ _ hpg,
    relativeFreeFiniteDeltaStep_map_prime_mul N σ D q hp,
    relativeFreeFiniteDeltaStep_map_generator_mul N σ D q hp d hd]

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaPerturbation

/-! ## 有限δ計算の核の二乗に関する不変性

有限δ計算は異なる有限環の間の写像である。
通常射との合成について、初期包含の核の二乗に属す誤差を消す。
-/

section RelativeFreeFiniteDeltaSquareCongruence

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type w} [CommRing B]
variable (N : ℕ) (σ : Type v)

/-- 初期包含の核の二乗の元は、有限δ計算の後も通常射で消える。 -/
theorem relativeFreeFiniteDeltaStep_map_zero_of_mem_ker_square (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f : MvPolynomial (σ × Fin (N + 1)) A)
    (hf : f ∈ (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) = 0 := by
  let I := RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))
  have hf' : f ∈ I * I := by simpa only [I, pow_two] using hf
  have he : q (relativeFreeFiniteStepInclusion N σ f) = 0 ∧
      q (relativeFreeFiniteDeltaStep N σ D f) = 0 := by
    refine Submodule.mul_induction_on (C := fun z =>
      q (relativeFreeFiniteStepInclusion N σ z) = 0 ∧
        q (relativeFreeFiniteDeltaStep N σ D z) = 0) hf' ?_ ?_
    · intro a ha b hb
      change q (relativeFreeFiniteStepInclusion N σ a) = 0 at ha
      change q (relativeFreeFiniteStepInclusion N σ b) = 0 at hb
      constructor
      · rw [map_mul, map_mul, ha, zero_mul]
      · rw [relativeFreeFiniteDeltaStep_map_mul_of_prime_zero N σ D q hp,
          ha, hb, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul, mul_zero, add_zero]
    · intro a b ha hb
      constructor
      · rw [map_add, map_add, ha.1, hb.1, add_zero]
      · rw [relativeFreeFiniteDeltaStep_map_add_of_left_zero N σ D q a b ha.1,
          ha.2, hb.2, add_zero]
  exact he.2

/-- 初期包含の核の二乗だけ異なる有限多項式のδ像は、通常射の下で一致する。 -/
theorem relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : f - g ∈ (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) =
      q (relativeFreeFiniteDeltaStep N σ D g) := by
  have hzero := relativeFreeFiniteDeltaStep_map_zero_of_mem_ker_square N σ D q hp (f - g) hfg
  have hinc : q (relativeFreeFiniteStepInclusion N σ (f - g)) = 0 := by
    exact (Ideal.pow_le_self (by decide : 2 ≠ 0)) hfg
  have he := relativeFreeFiniteDeltaStep_map_add_of_right_zero N σ D q g (f - g) hinc
  rw [add_sub_cancel, hzero, add_zero] at he
  exact he

/-- 二次誤差を含むp倍・d倍の正規形から、有限δ像の二つのp乗項を計算できる。 -/
theorem relativeFreeFiniteDeltaStep_map_of_normalForm (D : DeltaStructure p A)
    (q : MvPolynomial (σ × Fin (N + 2)) A →+* B)
    (hp : q (p : MvPolynomial (σ × Fin (N + 2)) A) = 0)
    (d : A) (hd : q (MvPolynomial.C d) = 0)
    (f r g h : MvPolynomial (σ × Fin (N + 1)) A)
    (hform : f - (r + (p : MvPolynomial (σ × Fin (N + 1)) A) * g + MvPolynomial.C d * h) ∈
      (RingHom.ker (q.comp (relativeFreeFiniteStepInclusion N σ))) ^ 2) :
    q (relativeFreeFiniteDeltaStep N σ D f) =
      q (relativeFreeFiniteDeltaStep N σ D r) +
        (q (relativeFreeFiniteStepInclusion N σ g)) ^ p +
          q (MvPolynomial.C (D.delta d)) *
            (q (relativeFreeFiniteStepInclusion N σ h)) ^ p := by
  rw [relativeFreeFiniteDeltaStep_map_eq_of_sub_mem_ker_square N σ D q hp _ _ hform]
  exact relativeFreeFiniteDeltaStep_map_perturbation N σ D q hp d hd r g h

end SerrePositivity.BhattScholze

end RelativeFreeFiniteDeltaSquareCongruence

/-! ## 有限δ計算とrank 1変数の補助δ計算の差

pを消す通常射の下で差は加法的で、Frobeniusを係数作用とするLeibniz公式を満たす。
-/

section RelativeFreeFiniteDeltaLinearization

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

end RelativeFreeFiniteDeltaLinearization
