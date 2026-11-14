module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.NumberTheory.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Function.Basic
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.Frobenius

/-!
# δ 環から Witt 環への写像（BS 著者版 Remark 2.7 の w_R、BS 著者版 Remark 2.13 の δ_n）

## 概要
ghost 座標が Frobenius 持ち上げの反復 φⁿ(a) になる Witt 係数の列を構成し、ghost 写像が単射のとき
環準同型 A → W(A) を与える。低次の係数、自然性、Witt の Frobenius との両立。BS 著者版 Remark 2.13。

## 方針
可除性 p^{n+1} ∣ φ^{n+1}(a) − (…) から係数を一段ずつ選ぶ。係数列の存在は p ねじれがあっても成り立つ。

## 規約
環準同型性・一意性は ghost 写像の単射性を仮定する。Joyal の右随伴としての普遍性は述べない。

## 使われ方
相対自由 δ 環の Witt 座標（Free/Finite、BS 著者版 Remark 2.14 の相対版）と、André の一段の拡大の Witt 方程式（Division/Relations）。
-/

@[expose] public noncomputable section
universe u v

/-! ## δFrobeniusのghost係数を一段延長する可除性

既存のp乗合同の可除性から、次のWitt ghost係数の存在を示す。
-/

section DeltaWittGhostStep

namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- δFrobeniusとp乗の合同は、p^k乗後にはp^(k+1)まで強まる。 -/
theorem frobeniusLift_pow_congruence (D : DeltaStructure p A) (a : A) (k : ℕ) :
    (p : A) ^ (k + 1) ∣ (D.frobeniusLift a) ^ (p ^ k) - (a ^ p) ^ (p ^ k) := by
  apply dvd_sub_pow_of_dvd_sub
  exact ⟨D.delta a, by rw [D.frobeniusLift_apply]; ring⟩

/-- 前段のghost等式から、次の係数を作る差はp^(n+1)で割り切れる。 -/
theorem ghost_next_dvd (D : DeltaStructure p A) (a : A) (b : ℕ → A) (n : ℕ)
    (hb : D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n - i))) :
    (p : A) ^ (n + 1) ∣ D.frobeniusLift^[n + 1] a -
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n + 1 - i)) := by
  rw [Function.iterate_succ_apply', hb, map_sum]
  simp only [map_mul, map_pow, map_natCast]
  rw [← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hexp : n + 1 - i = n - i + 1 := by omega
  rw [← mul_sub, hexp, pow_succ' p (n - i), pow_mul]
  have he : n + 1 = i + (n - i + 1) := by omega
  rw [he, pow_add]
  exact mul_dvd_mul_left _ (D.frobeniusLift_pow_congruence (b i) (n - i))

/-- 前段までの係数に、次のghost等式を満たす係数を追加できる。 -/
theorem exists_next_ghost_coefficient (D : DeltaStructure p A) (a : A) (b : ℕ → A) (n : ℕ)
    (hb : D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n - i))) :
    ∃ c : A, D.frobeniusLift^[n + 1] a =
      (∑ i ∈ Finset.range (n + 1), (p : A) ^ i * b i ^ (p ^ (n + 1 - i))) +
        (p : A) ^ (n + 1) * c := by
  obtain ⟨c, hc⟩ := D.ghost_next_dvd a b n hb
  refine ⟨c, ?_⟩
  rw [← hc]
  ring

end SerrePositivity.BhattScholze.DeltaStructure

end DeltaWittGhostStep

/-! ## δFrobeniusをghost座標に持つ全Witt係数の構成

有限prefixの延長で既定係数を保存し、整合した対角列を作る。
-/

section DeltaWittGhostCoefficients

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 既定係数を保存してghost等式を一段ずつ延長する有限prefix。 -/
def deltaWittGhostPrefix (D : DeltaStructure p A) (a : A) : ℕ → (ℕ → A)
  | 0 => fun _ => a
  | n + 1 => Function.update (deltaWittGhostPrefix D a n) (n + 1)
      (Classical.epsilon fun c => D.frobeniusLift^[n + 1] a =
        (∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
          (deltaWittGhostPrefix D a n i) ^ (p ^ (n + 1 - i))) +
          (p : A) ^ (n + 1) * c)

private theorem deltaWittGhostPrefix_succ_of_le (D : DeltaStructure p A) (a : A)
    (n i : ℕ) (hi : i ≤ n) : deltaWittGhostPrefix D a (n + 1) i = deltaWittGhostPrefix D a n i := by
  simp only [deltaWittGhostPrefix, Function.update_of_ne (by omega : i ≠ n + 1)]

private theorem deltaWittGhostPrefix_ghost (D : DeltaStructure p A) (a : A) (n : ℕ) :
    ∀ m ≤ n, D.frobeniusLift^[m] a =
      ∑ i ∈ Finset.range (m + 1), (p : A) ^ i * (deltaWittGhostPrefix D a n i) ^ (p ^ (m - i)) := by
  induction n with
  | zero =>
      intro m hm
      have hm0 : m = 0 := by omega
      subst m
      simp [deltaWittGhostPrefix]
  | succ n ih =>
      intro m hm
      by_cases hmn : m ≤ n
      · rw [ih m hmn]
        apply Finset.sum_congr rfl
        intro i hi
        rw [deltaWittGhostPrefix_succ_of_le D a n i (by have := Finset.mem_range.mp hi; omega)]
      · have hm' : m = n + 1 := by omega
        subst m
        have hc := Classical.epsilon_spec
          (D.exists_next_ghost_coefficient a (deltaWittGhostPrefix D a n) n (ih n le_rfl))
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, pow_zero, pow_one]
        have hs : (∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
            (deltaWittGhostPrefix D a (n + 1) i) ^ (p ^ (n + 1 - i))) =
            ∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
              (deltaWittGhostPrefix D a n i) ^ (p ^ (n + 1 - i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [deltaWittGhostPrefix_succ_of_le D a n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
        rw [hs]
        simpa only [deltaWittGhostPrefix, Function.update_self] using hc

private theorem deltaWittGhostPrefix_agrees (D : DeltaStructure p A) (a : A)
    (n i : ℕ) (hi : i ≤ n) :
    deltaWittGhostPrefix D a n i = deltaWittGhostPrefix D a i i := by
  induction n with
  | zero => have := Nat.eq_zero_of_le_zero hi; subst i; rfl
  | succ n ih =>
      by_cases hin : i ≤ n
      · rw [deltaWittGhostPrefix_succ_of_le D a n i hin, ih hin]
      · have h : i = n + 1 := by omega
        subst i
        rfl

/-- δFrobeniusの全反復をghost等式で実現する、具体的なWitt係数列。 -/
def deltaWittGhostCoefficients (D : DeltaStructure p A) (a : A) : ℕ → A :=
  fun n => deltaWittGhostPrefix D a n n

/-- 構成した全係数列のghost等式。p正則性や完備性は存在には不要。 -/
theorem deltaWittGhostCoefficients_ghost (D : DeltaStructure p A) (a : A) (n : ℕ) :
    D.frobeniusLift^[n] a =
      ∑ i ∈ Finset.range (n + 1), (p : A) ^ i *
        deltaWittGhostCoefficients D a i ^ (p ^ (n - i)) := by
  rw [deltaWittGhostPrefix_ghost D a n n le_rfl]
  apply Finset.sum_congr rfl
  intro i hi
  rw [deltaWittGhostPrefix_agrees D a n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rfl

/-- δFrobeniusを全ghost座標に持つ点ごとのWitt元。環射性は別工程。 -/
def deltaWittGhostVector (D : DeltaStructure p A) (a : A) : WittVector p A :=
  WittVector.mk p (deltaWittGhostCoefficients D a)

/-- 構成したWitt元の全ghost座標は基底Frobeniusの反復。 -/
theorem deltaWittGhostVector_ghostComponent (D : DeltaStructure p A) (a : A) (n : ℕ) :
    WittVector.ghostComponent n (deltaWittGhostVector D a) = D.frobeniusLift^[n] a := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.aeval_X,
    map_natCast, deltaWittGhostVector, WittVector.coeff_mk]
  exact (deltaWittGhostCoefficients_ghost D a n).symm

/-- 構成した点ごとのWitt元は第0係数射の断面になる。 -/
@[simp] theorem deltaWittGhostVector_coeff_zero (D : DeltaStructure p A) (a : A) :
    (deltaWittGhostVector D a).coeff 0 = a := rfl

end SerrePositivity.BhattScholze

end DeltaWittGhostCoefficients

/-! ## 構成したWitt元と既存W₂断面の比較

第1ghost公式とp乗算単射だけを用い、全ghost射の単射性は要求しない。
-/

section DeltaWittGhostLowCoefficients

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p乗算が単射なら、構成したWitt元の第1係数は既存δ写像に一致する。 -/
theorem deltaWittGhostVector_coeff_one (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    (deltaWittGhostVector D a).coeff 1 = D.delta a := by
  apply hp
  have he := deltaWittGhostVector_ghostComponent D a 1
  rw [witt_ghostComponent_one, deltaWittGhostVector_coeff_zero,
    Function.iterate_one, D.frobeniusLift_apply] at he
  rw [add_comm (a ^ p) ((p : A) * D.delta a)] at he
  exact add_right_cancel he

/-- p乗算単射下で、長さ2への切り詰めは既存のδ構造のW₂断面。 -/
theorem deltaWittGhostVector_truncate_two (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    WittVector.truncate 2 (deltaWittGhostVector D a) = D.sectionHom a := by
  apply TruncatedWittVector.ext
  intro i
  fin_cases i
  · rw [WittVector.coeff_truncate]
    change (deltaWittGhostVector D a).coeff 0 = (D.sectionHom a).coeff 0
    rw [deltaWittGhostVector_coeff_zero, D.coeff_zero]
  · rw [WittVector.coeff_truncate, deltaWittGhostVector_coeff_one D hp]
    rfl

end SerrePositivity.BhattScholze

end DeltaWittGhostLowCoefficients

/-! ## 第2Witt係数とδ二乗の三角形比較

p乗算単射を使い、下位座標から決まる補正を分離する。
-/

section DeltaWittGhostCoefficientTwo

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 第2Witt係数はδ²(a)と、a,δ(a)だけのp²可除性による補正の和。 -/
theorem deltaWittGhostVector_coeff_two_exists_correction (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a : A) :
    ∃ b : A, (deltaWittGhostVector D a).coeff 2 = D.delta (D.delta a) + b ∧
      (D.frobeniusLift a) ^ p - a ^ (p * p) = (p : A) ^ 2 * b := by
  have hd : (p : A) ^ 2 ∣ (D.frobeniusLift a) ^ p - a ^ (p * p) := by
    simpa only [pow_one, ← pow_mul] using D.frobeniusLift_pow_congruence a 1
  obtain ⟨b, hb⟩ := hd
  refine ⟨b, ?_, hb⟩
  have hc := deltaWittGhostCoefficients_ghost D a 2
  have hcoeff (i : ℕ) : deltaWittGhostCoefficients D a i = (deltaWittGhostVector D a).coeff i := rfl
  simp only [hcoeff, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.reduceSub, pow_zero, pow_one, one_mul, deltaWittGhostVector_coeff_zero,
    deltaWittGhostVector_coeff_one D hp] at hc
  have hf : D.frobeniusLift^[2] a = (D.frobeniusLift a) ^ p +
      (p : A) * (D.delta a) ^ p + (p : A) ^ 2 * D.delta (D.delta a) := by
    change D.frobeniusLift (D.frobeniusLift a) = _
    calc
      _ = (D.frobeniusLift a) ^ p + (p : A) * D.frobeniusLift (D.delta a) := by
        conv_lhs => rw [D.frobeniusLift_apply a]
        rw [map_add, map_pow, map_mul, map_natCast]
      _ = _ := by rw [D.frobeniusLift_apply (D.delta a)]; ring
  have hc' : D.frobeniusLift^[2] a = a ^ (p * p) +
      (p : A) * (D.delta a) ^ p + (p : A) ^ 2 * (deltaWittGhostVector D a).coeff 2 := by
    simpa only [pow_two] using hc
  apply hp
  apply hp
  linear_combination -hc' + hf + hb

/-- 下位座標から補正bを指定すれば、第2Witt係数はδ²(a)+bとなる。 -/
theorem deltaWittGhostVector_coeff_two_of_correction (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (a b : A)
    (hb : (D.frobeniusLift a) ^ p - a ^ (p * p) = (p : A) ^ 2 * b) :
    (deltaWittGhostVector D a).coeff 2 = D.delta (D.delta a) + b := by
  obtain ⟨c, hcoef, hc⟩ := deltaWittGhostVector_coeff_two_exists_correction D hp a
  have hcb : c = b := by
    apply hp
    apply hp
    simpa only [pow_two, mul_assoc] using hc.symm.trans hb
  rw [hcb] at hcoef
  exact hcoef

end SerrePositivity.BhattScholze

end DeltaWittGhostCoefficientTwo

/-! ## ghost射単射下でのδからWittへの環射

全係数構成の環射性をghost射の単射性へ明示的に相対化する。
-/

section DeltaWittGhostRingHom

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- ghost 写像が単射なら、Witt 写像 w_R は環準同型（BS 著者版 Remark 2.13 と Remark 2.7 の随伴単位の環準同型の部分）。 -/
def deltaWittGhostRingHom (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    A →+* WittVector p A where
  toFun := deltaWittGhostVector D
  map_one' := by
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_one, deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) 1 = 1
    exact map_one _
  map_mul' := by
    intro a b
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_mul,
      deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) (a * b) = (D.frobeniusLift ^ n) a * (D.frobeniusLift ^ n) b
    exact map_mul _ _ _
  map_zero' := by
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_zero, deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) 0 = 0
    exact map_zero _
  map_add' := by
    intro a b
    apply hg
    ext n
    simp only [WittVector.ghostMap_apply, map_add,
      deltaWittGhostVector_ghostComponent]
    change (D.frobeniusLift ^ n) (a + b) = (D.frobeniusLift ^ n) a + (D.frobeniusLift ^ n) b
    exact map_add _ _ _

/-- 構成した環射は第0係数環射の断面。 -/
theorem deltaWittGhostRingHom_constantCoeff_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    WittVector.constantCoeff.comp (deltaWittGhostRingHom D hg) = RingHom.id A := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_coeff_zero D a

/-- p乗算単射下では、新しい全Witt環射の長さ2切り詰めは既存δ断面。 -/
theorem deltaWittGhostRingHom_truncate_two_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hp : Function.Injective (fun a : A => (p : A) * a)) :
    (WittVector.truncate 2).comp (deltaWittGhostRingHom D hg) = D.sectionHom := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_truncate_two D hp a

/-- 全ghost成分を指定したWitt環射は、ghost射単射下で一意（BS 著者版 Remark 2.13 の ghost 写像が単射の場合の特徴づけ）。 -/
theorem deltaWittGhostRingHom_unique (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (f : A →+* WittVector p A)
    (hf : ∀ a n, WittVector.ghostComponent n (f a) = D.frobeniusLift^[n] a) :
    f = deltaWittGhostRingHom D hg := by
  apply RingHom.ext
  intro a
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply, hf]
  exact (deltaWittGhostVector_ghostComponent D a n).symm

end SerrePositivity.BhattScholze

end DeltaWittGhostRingHom

/-! ## δ射に関する構成済みWitt liftの自然性

終域のghost射の単射性だけで点ごとの比較を行う。
-/

section DeltaWittGhostNaturality

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

private theorem ghost_map_eval (f : A →+* B) (w : WittVector p A) (n : ℕ) :
    WittVector.ghostComponent n (WittVector.map f w) = f (WittVector.ghostComponent n w) := by
  simp only [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow,
    map_sum, map_mul, map_pow, MvPolynomial.aeval_X, map_natCast, WittVector.map_coeff]

/-- δ射によるWitt liftの点ごとの自然性。源のghost単射は不要。 -/
theorem deltaWittGhostVector_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) (a : A) :
    WittVector.map f (deltaWittGhostVector D a) = deltaWittGhostVector E (f a) := by
  have hi (n : ℕ) : f (D.frobeniusLift^[n] a) = E.frobeniusLift^[n] (f a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hf.map_frobeniusLift, ih]
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply, ghost_map_eval,
    deltaWittGhostVector_ghostComponent, deltaWittGhostVector_ghostComponent]
  exact hi n

/-- 全係数の自然性。自由初期変数の三角形表示をδ反復へ評価する際に使う。 -/
theorem deltaWittGhostVector_coeff_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) (a : A) (n : ℕ) :
    f ((deltaWittGhostVector D a).coeff n) = (deltaWittGhostVector E (f a)).coeff n := by
  have he := congrArg (fun w : WittVector p B => w.coeff n) (deltaWittGhostVector_map D E f hf hg a)
  simpa only [WittVector.map_coeff] using he

/-- 構成した全Witt環射の自然性の具体的な図式。 -/
theorem deltaWittGhostRingHom_map_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f)
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgB : Function.Injective (WittVector.ghostMap : WittVector p B → ℕ → B)) :
    (WittVector.map f).comp (deltaWittGhostRingHom D hgA) =
      (deltaWittGhostRingHom E hgB).comp f := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_map D E f hf hgB a

end SerrePositivity.BhattScholze

end DeltaWittGhostNaturality

/-! ## 構成したWitt写像のFrobenius図式とδ方程式

ghost成分の一段シフトを使い、δ構造を要求しない終域への係数射も扱う。
-/

section DeltaWittGhostFrobenius

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- ghost射単射下では、構成したWitt元のFrobeniusは基底φの像。 -/
theorem deltaWittGhostVector_frobenius (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) :
    WittVector.frobenius (deltaWittGhostVector D a) =
      deltaWittGhostVector D (D.frobeniusLift a) := by
  apply hg
  funext n
  rw [WittVector.ghostMap_apply, WittVector.ghostMap_apply,
    WittVector.ghostComponent_frobenius, deltaWittGhostVector_ghostComponent,
    deltaWittGhostVector_ghostComponent]
  exact Function.iterate_succ_apply D.frobeniusLift n a

/-- 全Witt環射は基底FrobeniusとWitt Frobeniusを絡める。 -/
theorem deltaWittGhostRingHom_frobenius_comp (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) :
    WittVector.frobenius.comp (deltaWittGhostRingHom D hg) =
      (deltaWittGhostRingHom D hg).comp D.frobeniusLift := by
  apply RingHom.ext
  intro a
  exact deltaWittGhostVector_frobenius D hg a

/-- 基底δを使うFrobenius方程式（BS 著者版 Remark 2.13 の ghost 写像が単射の場合の φ と δ の関係）。
  全Witt係数を追うための具体的な式。 -/
theorem deltaWittGhostVector_frobenius_formula (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A)) (a : A) :
    WittVector.frobenius (deltaWittGhostVector D a) =
      (deltaWittGhostVector D a) ^ p +
        (p : WittVector p A) * deltaWittGhostVector D (D.delta a) := by
  rw [deltaWittGhostVector_frobenius D hg]
  change (deltaWittGhostRingHom D hg) (D.frobeniusLift a) = _
  rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, map_natCast]
  rfl

/-- 任意通常係数射によるδ方程式の像。終域のδ構造は要求しない。 -/
theorem deltaWittGhostVector_frobenius_formula_map {B : Type v} [CommRing B]
    (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (q : A →+* B) (a : A) :
    WittVector.map q (WittVector.frobenius (deltaWittGhostVector D a)) =
      (WittVector.map q (deltaWittGhostVector D a)) ^ p +
        (p : WittVector p B) * WittVector.map q (deltaWittGhostVector D (D.delta a)) := by
  rw [deltaWittGhostVector_frobenius_formula D hg, map_add, map_pow, map_mul, map_natCast]

end SerrePositivity.BhattScholze

end DeltaWittGhostFrobenius

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Rem 2.13"] _root_.SerrePositivity.BhattScholze.deltaWittGhostRingHom
attribute [cite BS19 "Rem 2.13"] _root_.SerrePositivity.BhattScholze.deltaWittGhostRingHom_unique
attribute [cite BS19 "Rem 2.13"] _root_.SerrePositivity.BhattScholze.deltaWittGhostVector_frobenius_formula
attribute [cite BS19 "Rem 2.7" (partial := special) "通常のテンソル積（p 正則性なし、BS-W15）、有向余極限、完全 δ 環のテンソル、w_R : R → W(R)（ghost 単射かつ p ねじれなしのとき）。一般の極限・余極限、W が右随伴であることは未 ／ DOC1 照合：ok 4 件 ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaWittGhostRingHom
