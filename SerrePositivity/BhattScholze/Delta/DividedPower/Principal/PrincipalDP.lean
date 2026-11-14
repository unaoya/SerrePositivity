module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import SerrePositivity.CommutativeAlgebra.DividedPowers.RankOneDP
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import Mathlib.Tactic.Ring
public import SerrePositivity.BhattScholze.Delta.DividedPower.PDivision.PDivision
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionQuotient
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# 一元の pd 包（BS 著者版 Lemma 2.38 の r = 1）

## 概要
一元分冪表示環 Γ_B⟨T⟩/(T − y) と任意の分冪標的への評価、係数環への評価テンソル、底変換とその関係式・普遍性、階乗部分環への全射とその核（p 冪ねじれ）・同型、mod p 比較と標数 p での忠実平坦性、正則入力での p 正則性、元の係数環上の導来完備化・導来底変換・p Koszul 比較、正則一元階乗部分環の底変換・mod p 比較・普遍射。

## 方針
原典の BS 著者版 Lemma 2.38 を r = 1 で、離散性・p ねじれなし・pd 包との同一視・底変換・mod p の自由性まで示す。一般の有限正則列の場合は BS 著者版 Lemma 2.38 の系列で扱う。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`、`Andre/PowerRootEnvelope/DividedPowerPrime`、`Andre/PowerRootEnvelope/PrincipalDP`。
-/

universe u v

/-! ## 一元分冪表示環と任意の分冪標的への評価

既存のDividedPowerAlgebraにγ₁(1)=yを課す。
このファイルは表示環自身の分冪構造や分冪包との同型を主張しない。
-/

@[expose] public noncomputable section PrincipalDPPresentation

namespace SerrePositivity.BhattScholze
variable {A : Type u} [CommRing A]

/-- 既存分冪代数内の、γ₁(1)=yを課す具体的な関係イデアル。 -/
def principalDPRelationIdeal (y : A) : Ideal (DividedPowerAlgebra A A) :=
  Ideal.span {DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y}

/-- 一元yに対する具体的分冪表示環。分冪構造の存在はこの定義には含めない。 -/
abbrev PrincipalDPPresentation (A : Type u) [CommRing A] (y : A) :=
  DividedPowerAlgebra A A ⧸ principalDPRelationIdeal y

/-- 表示環内のγ_n(1)の標準像。 -/
def principalDPGenerator (y : A) (n : ℕ) : PrincipalDPPresentation A y :=
  Ideal.Quotient.mk (principalDPRelationIdeal y) (DividedPowerAlgebra.dp A n (1 : A))

/-- 課した一次関係が実商環で成立する。 -/
theorem principalDPGenerator_one (y : A) :
    principalDPGenerator y 1 = algebraMap A (PrincipalDPPresentation A y) y := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (principalDPRelationIdeal y)
    (DividedPowerAlgebra.dp A 1 (1 : A)) -
      Ideal.Quotient.mk (principalDPRelationIdeal y)
        (algebraMap A (DividedPowerAlgebra A A) y) = 0
  rw [← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 表示環内での、全次数の具体的階乗恒等式。 -/
theorem principalDPGenerator_factorial_mul (y : A) (n : ℕ) :
    (n.factorial : PrincipalDPPresentation A y) * principalDPGenerator y n =
      (algebraMap A (PrincipalDPPresentation A y) y) ^ n := by
  have h := congrArg (Ideal.Quotient.mk (principalDPRelationIdeal y))
    (DividedPowerAlgebra.natFactorial_mul_dp_eq (R := A) n (1 : A))
  simp only [map_mul, map_natCast, map_pow] at h
  change (n.factorial : PrincipalDPPresentation A y) * principalDPGenerator y n =
    principalDPGenerator y 1 ^ n at h
  simpa only [principalDPGenerator_one] using h

/-- 任意の分冪標的への実評価射。ねじれや正則性の仮定を置かない。 -/
def principalDPEval {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A)
    (hy : algebraMap A B y ∈ I) : PrincipalDPPresentation A y →ₐ[A] B := by
  let g : A →ₗ[A] B := LinearMap.toSpanSingleton A B (algebraMap A B y)
  have hg : ∀ a, g a ∈ I := by
    intro a
    change a • algebraMap A B y ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hy
  let F := DividedPowerAlgebra.lift H g hg
  refine Ideal.Quotient.liftₐ (principalDPRelationIdeal y) F ?_
  have hker : principalDPRelationIdeal y ≤ RingHom.ker F.toRingHom := by
    apply Ideal.span_le.mpr
    rintro t (rfl : t = _)
    change F (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y) = 0
    rw [map_sub, DividedPowerAlgebra.lift_apply_dp]
    simp only [g, LinearMap.toSpanSingleton_apply_one, H.dpow_one hy, AlgHom.commutes,
      sub_self]
  intro a ha
  exact hker ha

/-- 実評価射は全標準生成元を指定した分冪値へ送る。 -/
theorem principalDPEval_generator {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A)
    (hy : algebraMap A B y ∈ I) (n : ℕ) :
    principalDPEval H y hy (principalDPGenerator y n) = H.dpow n (algebraMap A B y) := by
  change DividedPowerAlgebra.lift H
    (LinearMap.toSpanSingleton A B (algebraMap A B y))
    (by
      intro a
      change a • algebraMap A B y ∈ I
      rw [Algebra.smul_def]
      exact I.mul_mem_left _ hy)
    (DividedPowerAlgebra.dp A n (1 : A)) = _
  rw [DividedPowerAlgebra.lift_apply_dp, LinearMap.toSpanSingleton_apply_one]

/-- 全γ_n(1)上の値は表示環からの代数射を一意に決める。 -/
theorem principalDPHom_ext {B : Type v} [CommRing B] [Algebra A B] (y : A)
    (F G : PrincipalDPPresentation A y →ₐ[A] B)
    (h : ∀ n, F (principalDPGenerator y n) = G (principalDPGenerator y n)) : F = G := by
  apply Ideal.Quotient.algHom_ext
  apply DividedPowerAlgebra.algHom_ext
  intro n a
  have ha : DividedPowerAlgebra.dp A n a =
      a ^ n • DividedPowerAlgebra.dp A n (1 : A) := by
    simpa only [smul_eq_mul, mul_one] using
      (DividedPowerAlgebra.dp_smul (R := A) (r := a) (n := n) (m := (1 : A)))
  rw [ha]
  simp only [map_smul, AlgHom.comp_apply]
  exact congrArg (fun b : B ↦ a ^ n • b) (h n)

/-- ねじれを許す任意の分冪標的に対して、指定した生成元値を持つ評価射は一意に存在する。 -/
theorem existsUnique_principalDPEval {B : Type v} [CommRing B] [Algebra A B]
    {I : Ideal B} (H : DividedPowers I) (y : A) (hy : algebraMap A B y ∈ I) :
    ∃! F : PrincipalDPPresentation A y →ₐ[A] B,
      ∀ n, F (principalDPGenerator y n) = H.dpow n (algebraMap A B y) := by
  refine ⟨principalDPEval H y hy, principalDPEval_generator H y hy, ?_⟩
  intro F hF
  apply principalDPHom_ext y
  intro n
  exact (hF n).trans (principalDPEval_generator H y hy n).symm

end SerrePositivity.BhattScholze

end PrincipalDPPresentation

/-! ## 正則一元入力での実分冪表示環のp正則性 -/

@[expose] public noncomputable section PrincipalDPRegular

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
local notation "B₀" => DividedPowerAlgebra A A

/-- 一元分冪代数の一次生成元のp乗はpで割れる。 -/
theorem rankOneDPGenerator_pow_mem_prime :
    (DividedPowerAlgebra.dp A 1 (1 : A)) ^ p ∈ Ideal.span {(p : B₀)} := by
  rw [← DividedPowerAlgebra.natFactorial_mul_dp_eq]
  apply Ideal.mul_mem_right
  apply Ideal.mem_span_singleton.mpr
  exact map_dvd (Nat.castRingHom B₀)
    (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl)

/-- p乗算が単射でy mod pが正則なら、表示関係もmod pで正則。p局所性は不要。 -/
theorem principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)})
        (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)) := by
  let : Module.Free A B₀ := rankOneDPAny_moduleFree A
  let q := Ideal.Quotient.mk (Ideal.span {(p : B₀)})
  let x := q (DividedPowerAlgebra.dp A 1 (1 : A))
  let c := q (algebraMap A B₀ y)
  have hc : IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)}) c := by
    have h := SerrePositivity.isSMulRegular_mod_of_flat (S := B₀) (p : A) y hpA hy
    have aux (a : B₀) (he : a = (p : B₀))
        (ha : IsSMulRegular (B₀ ⧸ Ideal.span {a})
          (Ideal.Quotient.mk (Ideal.span {a}) (algebraMap A B₀ y))) :
        IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)}) c := by
      subst a
      exact ha
    exact aux _ (map_natCast (algebraMap A B₀) p) h
  have hx : x ^ p = 0 := by
    change q (DividedPowerAlgebra.dp A 1 (1 : A)) ^ p = 0
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr rankOneDPGenerator_pow_mem_prime
  change Function.Injective (fun z : B₀ ⧸ Ideal.span {(p : B₀)} ↦ q
    (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y) * z)
  simp only [map_sub]
  change Function.Injective (fun z : B₀ ⧸ Ideal.span {(p : B₀)} ↦ (x - c) * z)
  intro z t hzt
  apply sub_eq_zero.mp
  have hxc : x * (z - t) = c * (z - t) := by
    apply sub_eq_zero.mp
    rw [← sub_mul, mul_sub]
    exact sub_eq_zero.mpr hzt
  have hn : ∀ n : ℕ, x ^ n * (z - t) = c ^ n * (z - t) := by
    intro n
    induction n with
    | zero => simp only [pow_zero, one_mul]
    | succ n ih =>
        calc
          _ = x ^ n * (x * (z - t)) := by ring
          _ = x ^ n * (c * (z - t)) := by rw [hxc]
          _ = c * (x ^ n * (z - t)) := by ring
          _ = c * (c ^ n * (z - t)) := by rw [ih]
          _ = _ := by ring
  apply hc.pow p
  change c ^ p * (z - t) = c ^ p * 0
  rw [mul_zero, ← hn p, hx, zero_mul]

set_option linter.unusedVariables false in
/-- y mod pが正則なら、表示関係γ₁(1)−yも一元分冪代数のmod pで正則。 -/
theorem principalDPRelation_mod_p_isSMulRegular
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    IsSMulRegular (B₀ ⧸ Ideal.span {(p : B₀)})
      (Ideal.Quotient.mk (Ideal.span {(p : B₀)})
        (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)) :=
  principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective hpA y hy

/-- p乗算が単射でy mod pが正則なら、具体的分冪表示環もp正則。p局所性は不要。 -/
theorem principalDPPresentation_p_mul_injective_of_regular_mod
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    Function.Injective (fun b : PrincipalDPPresentation A y ↦
      (p : PrincipalDPPresentation A y) * b) := by
  have hp : IsSMulRegular B₀ (p : B₀) := by
    simpa only [map_natCast] using rankOneDPAny_isSMulRegular (p : A) hpA
  have h := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod B₀ (p : B₀)
    (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A B₀ y)
    hp
    (principalDPRelation_mod_p_isSMulRegular_of_p_mul_injective hpA y hy)
  simpa only [IsSMulRegular, smul_eq_mul, map_natCast, PrincipalDPPresentation,
    principalDPRelationIdeal] using h

set_option linter.unusedVariables false in
/-- 正則一元入力の下で、具体的分冪表示環にはpねじれがない（BS 著者版 Lemma 2.38 の一元 PD 表示の p 正則性）。 -/
theorem principalDPPresentation_p_mul_injective
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : A)
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    Function.Injective (fun b : PrincipalDPPresentation A y ↦
      (p : PrincipalDPPresentation A y) * b) :=
  principalDPPresentation_p_mul_injective_of_regular_mod hpA y hy

end SerrePositivity.BhattScholze

end PrincipalDPRegular

/-! ## 一元分冪表示環から具体的階乗部分環への実全射

源のpねじれを許す。単射性や導来比較はこのファイルの結論には含まない。
-/

@[expose] public noncomputable section PrincipalDPToFactorial

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実分冪構造への評価が与える、一元表示環から具体的階乗部分環への環射。 -/
def principalDPToFactorial (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) :
    PrincipalDPPresentation A y →+* pDivisionFactorialSubring p (fun _ : Unit ↦ y) := by
  letI : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  exact (principalDPEval (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())).toRingHom

/-- 表示環からの実射は、元のAからの基底射を保つ。 -/
theorem principalDPToFactorial_coeff (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y a : A) :
    principalDPToFactorial hA D y (algebraMap A (PrincipalDPPresentation A y) a) =
      pDivisionFactorialBase p (fun _ : Unit ↦ y) a := by
  let : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  exact AlgHom.commutes (principalDPEval
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())) a

/-- 各標準生成元の実像は、局所化内の指定された階乗分母。 -/
theorem principalDPToFactorial_generator (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) (n : ℕ) :
    principalDPToFactorial hA D y (principalDPGenerator y n) =
      ⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ := by
  let : Algebra A (pDivisionFactorialSubring p (fun _ : Unit ↦ y)) :=
    (pDivisionFactorialBase p (fun _ : Unit ↦ y)).toAlgebra
  have h := principalDPEval_generator
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ()) n
  apply Subtype.ext
  change (principalDPEval
    (pDivisionFactorialIdealDividedPowers hA D (fun _ : Unit ↦ y)) y
    (pDivisionFactorialBase_mem_factorialIdeal (fun _ : Unit ↦ y) ())
    (principalDPGenerator y n) : Localization.Away (p : A)) = _
  rw [h]
  exact pDivisionFactorialIdealDividedPowers_base_apply hA D (fun _ : Unit ↦ y) () n

/-- 一元分冪表示環から具体的階乗部分環への実射は全射。 -/
theorem principalDPToFactorial_surjective (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : A) : Function.Surjective (principalDPToFactorial hA D y) := by
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  let F := principalDPToFactorial hA D y
  have hle : S ≤ (S.subtype.comp F).range := by
    apply Subring.closure_le.mpr
    rintro t (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · refine ⟨algebraMap A (PrincipalDPPresentation A y) a, ?_⟩
      exact congrArg Subtype.val (principalDPToFactorial_coeff hA D y a)
    · refine ⟨principalDPGenerator y n, ?_⟩
      exact congrArg Subtype.val (principalDPToFactorial_generator hA D y n)
  rintro ⟨t, ht⟩
  obtain ⟨b, hb⟩ := hle ht
  exact ⟨b, Subtype.ext hb⟩

end SerrePositivity.BhattScholze

end PrincipalDPToFactorial

/-! ## 一元表示環から階乗部分環への全射の核

核を実p局所化の核へ同定する。表示環のp正則性はこのファイルでは主張しない。
-/

@[expose] public noncomputable section PrincipalDPFactorialKernel

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実全射で零になる元は、表示環をp局所化しても零になる。 -/
theorem principalDPToFactorial_ker_le_away_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (principalDPToFactorial hA D y) ≤
      RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) := by
  let R := PrincipalDPPresentation A y
  let L := Localization.Away (p : R)
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  have hpL : IsUnit (algebraMap A L (p : A)) := by
    have hp := IsLocalization.Away.algebraMap_isUnit (S := L) (p : R)
    have hc : algebraMap R L (p : R) = (p : L) := map_natCast (algebraMap R L) p
    rw [hc] at hp
    simpa only [map_natCast] using hp
  let g : Localization.Away (p : A) →+* L :=
    IsLocalization.Away.lift (p : A) hpL
  let F : R →ₐ[A] L :=
    { toRingHom := g.comp (S.subtype.comp (principalDPToFactorial hA D y))
      commutes' := by
        intro a
        change g (principalDPToFactorial hA D y (algebraMap A R a) : Localization.Away (p : A)) = _
        rw [principalDPToFactorial_coeff]
        exact IsLocalization.Away.lift_eq (p : A) hpL a }
  let q : R →ₐ[A] L := IsScalarTower.toAlgHom A R L
  have hR : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : R) := by
    intro m hm
    simpa only [map_natCast] using (hA m hm).map (algebraMap A R)
  have hF : F = q := by
    apply principalDPHom_ext y
    intro n
    apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hR n.factorial
      (Nat.factorial_ne_zero n)).mul_left_cancel
    have h₁ := congrArg F (principalDPGenerator_factorial_mul y n)
    have h₂ := congrArg q (principalDPGenerator_factorial_mul y n)
    have hFn : F (n.factorial : R) = (n.factorial : L) := map_natCast F _
    have hqn : q (n.factorial : R) = (n.factorial : L) := map_natCast q _
    have hFy : F (algebraMap A R y) = algebraMap A L y := F.commutes y
    have hqy : q (algebraMap A R y) = algebraMap A L y := q.commutes y
    simp only [map_mul, map_pow, hFn, hqn] at h₁ h₂
    change (n.factorial : L) * F (principalDPGenerator y n) =
      F (algebraMap A R y) ^ n at h₁
    change (n.factorial : L) * q (principalDPGenerator y n) =
      q (algebraMap A R y) ^ n at h₂
    rw [hFy] at h₁
    rw [hqy] at h₂
    exact h₁.trans h₂.symm
  intro b hb
  have hb0 : principalDPToFactorial hA D y b = 0 := hb
  change q b = 0
  rw [← hF]
  change g ((principalDPToFactorial hA D y b : S) : Localization.Away (p : A)) = 0
  rw [hb0]
  exact map_zero g

/-- 階乗部分環のp正則性により、表示環のp冪ねじれは実全射で零になる。 -/
theorem principalDPToFactorial_away_ker_le_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) ≤
      RingHom.ker (principalDPToFactorial hA D y) := by
  let R := PrincipalDPPresentation A y
  let S := pDivisionFactorialSubring p (fun _ : Unit ↦ y)
  let F := principalDPToFactorial hA D y
  intro b hb
  obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (p : R)) (Localization.Away (p : R)) b).mp hb
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : R) (p : R)).mp c.property
  have hr : IsLeftRegular (p : S) := pDivisionFactorial_p_mul_injective (fun _ : Unit ↦ y)
  have he : (p : S) ^ n * F b = (p : S) ^ n * 0 := by
    rw [mul_zero]
    have h := congrArg F hc
    rw [← hn] at h
    simpa only [map_mul, map_pow, map_natCast, map_zero] using h
  exact (hr.pow n) he

/-- 核は正確に表示環の実p局所化の核である。 -/
theorem principalDPToFactorial_ker_eq_away_ker
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A) :
    RingHom.ker (principalDPToFactorial hA D y) =
      RingHom.ker (algebraMap (PrincipalDPPresentation A y)
        (Localization.Away (p : PrincipalDPPresentation A y))) :=
  le_antisymm (principalDPToFactorial_ker_le_away_ker hA D y)
    (principalDPToFactorial_away_ker_le_ker hA D y)


/-- 実全射で零になることは、表示環であるp冪により消えることと同値。 -/
theorem principalDPToFactorial_eq_zero_iff
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : A)
    (b : PrincipalDPPresentation A y) :
    principalDPToFactorial hA D y b = 0 ↔
      ∃ n : ℕ, (p : PrincipalDPPresentation A y) ^ n * b = 0 := by
  change b ∈ RingHom.ker (principalDPToFactorial hA D y) ↔ _
  rw [principalDPToFactorial_ker_eq_away_ker]
  change algebraMap (PrincipalDPPresentation A y)
    (Localization.Away (p : PrincipalDPPresentation A y)) b = 0 ↔ _
  rw [IsLocalization.map_eq_zero_iff (Submonoid.powers (p : PrincipalDPPresentation A y))]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : PrincipalDPPresentation A y)
      (p : PrincipalDPPresentation A y)).mp c.property
    exact ⟨n, by simpa only [hn] using hc⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨(p : PrincipalDPPresentation A y) ^ n, ⟨n, rfl⟩⟩, hn⟩

end SerrePositivity.BhattScholze

end PrincipalDPFactorialKernel

/-! ## 正則一元分冪表示環と具体的階乗部分環の実同型 -/

@[expose] public noncomputable section PrincipalDPFactorialEquiv

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))

include hpA hy

/-- 正則一元入力では、表示環から階乗部分環への実比較射は単射。 -/
theorem principalDPToFactorial_injective : Function.Injective (principalDPToFactorial hA D y) := by
  intro b c hbc
  apply sub_eq_zero.mp
  have hz : principalDPToFactorial hA D y (b - c) = 0 := by
    rw [map_sub, hbc, sub_self]
  obtain ⟨n, hn⟩ := (principalDPToFactorial_eq_zero_iff hA D y (b - c)).mp hz
  have hr : IsLeftRegular (p : PrincipalDPPresentation A y) :=
    principalDPPresentation_p_mul_injective hA hpA y hy
  apply hr.pow n
  change (p : PrincipalDPPresentation A y) ^ n * (b - c) =
    (p : PrincipalDPPresentation A y) ^ n * 0
  rw [mul_zero]
  exact hn

/-- 正則一元表示環と具体的階乗部分環の、実比較射による環同型（BS 著者版 Lemma 2.38 の一元の場合の具体的同定）。 -/
def principalDPFactorialEquiv :
    PrincipalDPPresentation A y ≃+* pDivisionFactorialSubring p (fun _ : Unit ↦ y) :=
  RingEquiv.ofBijective (principalDPToFactorial hA D y)
    ⟨principalDPToFactorial_injective hA hpA D y hy, principalDPToFactorial_surjective hA D y⟩

/-- 実比較同型は元の係数環の射を保つ。 -/
theorem principalDPFactorialEquiv_coeff (a : A) :
    principalDPFactorialEquiv hA hpA D y hy (algebraMap A (PrincipalDPPresentation A y) a) =
      pDivisionFactorialBase p (fun _ : Unit ↦ y) a :=
  principalDPToFactorial_coeff hA D y a

/-- 実比較同型は全標準分冪生成元を指定された階乗分母へ送る。 -/
theorem principalDPFactorialEquiv_generator (n : ℕ) :
    principalDPFactorialEquiv hA hpA D y hy (principalDPGenerator y n) =
      ⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ :=
  principalDPToFactorial_generator hA D y n

end SerrePositivity.BhattScholze

end PrincipalDPFactorialEquiv

/-! ## 元の係数環上での正則分冪表示環のp Koszul比較 -/

@[expose] public noncomputable section PrincipalDPRelativeModPKoszul

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "J₀" => Ideal.span {(p : R₀)}
local notation "Q₀" => R₀ ⧸ J₀

/-- 具体的表示環のp列を、元の係数環A上の短複体として取る。 -/
def principalDPRelativeModPPresentation : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk ((p : A) • 𝟙 (ModuleCat.of A R₀))
    (ModuleCat.ofHom (Ideal.Quotient.mkₐ A J₀).toLinearMap) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change Ideal.Quotient.mk J₀ ((p : A) • r) = 0
      rw [Algebra.smul_def, map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))))

variable [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))

include hA hpA hy in
/-- 正則入力では、この実p列は元のA加群の短完全列。 -/
theorem principalDPRelativeModPPresentation_shortExact :
    (principalDPRelativeModPPresentation (p := p) y).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro r hr
    change Ideal.Quotient.mk J₀ r = 0 at hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    refine ⟨s, ?_⟩
    change (p : A) • s = r
    rw [Algebra.smul_def, map_natCast]
    exact hs.symm
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    intro r s hrs
    apply principalDPPresentation_p_mul_injective hA hpA y hy
    change (p : A) • r = (p : A) • s at hrs
    have hmul (t : R₀) : (p : A) • t = (p : R₀) * t := by
      rw [Algebra.smul_def, map_natCast]
    exact (hmul r).symm.trans (hrs.trans (hmul s))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    change Function.Surjective (Ideal.Quotient.mk J₀)
    exact Ideal.Quotient.mk_surjective)

/-- 実p列を元のA加群の次数零cochain複体へ送る。 -/
def principalDPRelativeModPCochainPresentation :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  (principalDPRelativeModPPresentation (p := p) y).map
    (CochainComplex.singleFunctor (ModuleCat A) 0)

omit [Fact p.Prime] in
/-- 最初のcochain射は、元のAのpによるスカラー射そのもの。 -/
theorem principalDPRelativeModPCochainPresentation_f :
    (principalDPRelativeModPCochainPresentation (p := p) y).f =
      smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀)) := by
  change (CochainComplex.singleFunctor (ModuleCat A) 0).map
    ((p : A) • 𝟙 (ModuleCat.of A R₀)) = _
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- A上の実p Koszul coneから、実p商の次数零対象への標準添加写像。 -/
def principalDPRelativeModPKoszulAugmentation :
    CochainComplex.mappingCone (smulId (p : A) (cochainSingleZero (ModuleCat.of A R₀))) ⟶
      cochainSingleZero (ModuleCat.of A Q₀) :=
  eqToHom (congrArg (fun f : cochainSingleZero (ModuleCat.of A R₀) ⟶
      cochainSingleZero (ModuleCat.of A R₀) ↦ CochainComplex.mappingCone f)
        (principalDPRelativeModPCochainPresentation_f (p := p) y).symm) ≫
    CochainComplex.mappingCone.descShortComplex (principalDPRelativeModPCochainPresentation y)

include hA hpA hy in
/-- 正則入力では、元のA上の実Koszul添加写像が擬同型となる。 -/
theorem principalDPRelativeModPKoszulAugmentation_quasiIso :
    QuasiIso (principalDPRelativeModPKoszulAugmentation (p := p) y) := by
  have hS : (principalDPRelativeModPCochainPresentation (p := p) y).ShortExact :=
    (principalDPRelativeModPPresentation_shortExact y hA hpA hy).map_of_exact
      (CochainComplex.singleFunctor (ModuleCat A) 0)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  dsimp only [principalDPRelativeModPKoszulAugmentation]
  infer_instance

/-- 元のA→A/pで実導来還元した表示環をAへ制限すると、実R/pの次数零対象になる。 -/
def principalDPRelativeDerivedModPRestrictedIso :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A)}))).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)))).obj ≅
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Q₀)).obj := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  have hr : IsSMulRegular A (p : A) := hpA
  have := principalDPRelativeModPKoszulAugmentation_quasiIso y hA hpA hy
  exact restrictedDerivedQuotientKoszulIso (p : A) hr X ≪≫
    (DerivedCompletion.derivedScalarConeComparison A (p : A)).app
      (cochainSingleZero (ModuleCat.of A R₀)) ≪≫
    asIso (DerivedCategory.Q.map (principalDPRelativeModPKoszulAugmentation y))

end SerrePositivity.BhattScholze

end PrincipalDPRelativeModPKoszul

/-! ## 一元分冪表示の関係式と標準基底変更射

係数環の正則性を仮定せず、標準比較射が一次関係を保つことを示す。
-/

@[expose] public noncomputable section PrincipalDPBaseChangeRelations

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 実一元分冪基底変更射は、指定された表示関係を対応する関係へ送る。 -/
theorem rankOneDPBaseChangeMap_relation (y : A) :
    rankOneDPBaseChangeMap ((1 : B) ⊗ₜ[A]
      (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A (DividedPowerAlgebra A A) y)) =
      DividedPowerAlgebra.dp B 1 (1 : B) -
        algebraMap B (DividedPowerAlgebra B B) (algebraMap A B y) := by
  rw [TensorProduct.tmul_sub, map_sub, rankOneDPBaseChangeMap_dp,
    rankOneDPBaseChangeMap_tmul, map_one, one_mul]
  exact congrArg (fun t ↦ DividedPowerAlgebra.dp B 1 (1 : B) - t)
    ((DividedPowerAlgebra.map B (Algebra.linearMap A B)).commutes y)

end SerrePositivity.BhattScholze

end PrincipalDPBaseChangeRelations

/-! ## 一元分冪表示環の任意係数への実基底変更

係数環のpねじれを制限しない。既存の仮定付きAPIは変更しない。
-/

@[expose] public noncomputable section PrincipalDPBaseChangeUniversal

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- 任意係数への実基底変更で、拡大した表示関係イデアルが標的の関係イデアルに一致する。 -/
theorem principalDPBaseChangeUniversal_relationIdeal (y : A) :
    principalDPRelationIdeal (algebraMap A B y) =
      ((principalDPRelationIdeal y).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
          (rankOneDPBaseChangeUniversalEquiv (A := A) (B := B)).toRingHom := by
  rw [Ideal.map_map]
  simp only [principalDPRelationIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  congr 1
  exact (rankOneDPBaseChangeMap_relation (B := B) y).symm

/-- 一元分冪表示環の、任意の可換係数環への実テンソル基底変更同型（BS 著者版 Lemma 2.38 の一元の場合の古典的底変換）。 -/
def principalDPBaseChangeUniversalEquiv (y : A) :
    B ⊗[A] PrincipalDPPresentation A y ≃ₐ[B]
      PrincipalDPPresentation B (algebraMap A B y) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B (DividedPowerAlgebra A A) B
    (principalDPRelationIdeal y)).trans
    (Ideal.quotientEquivAlg _ _ rankOneDPBaseChangeUniversalEquiv
      (principalDPBaseChangeUniversal_relationIdeal (B := B) y))

/-- 一般基底変更同型はBの係数を保つ。 -/
theorem principalDPBaseChangeUniversalEquiv_coeff (y : A) (b : B) :
    principalDPBaseChangeUniversalEquiv (A := A) y
      (b ⊗ₜ[A] (1 : PrincipalDPPresentation A y)) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b :=
  (principalDPBaseChangeUniversalEquiv y).commutes b

/-- 一般基底変更同型の全標準生成元の純テンソル上の式。 -/
theorem principalDPBaseChangeUniversalEquiv_tmul_generator (y : A) (b : B) (n : ℕ) :
    principalDPBaseChangeUniversalEquiv y (b ⊗ₜ[A] principalDPGenerator y n) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b *
        principalDPGenerator (algebraMap A B y) n := by
  dsimp only [principalDPBaseChangeUniversalEquiv, principalDPGenerator]
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk (principalDPRelationIdeal (algebraMap A B y))
    (rankOneDPBaseChangeUniversalEquiv
      (b ⊗ₜ[A] DividedPowerAlgebra.dp A n (1 : A))) = _
  rw [rankOneDPBaseChangeUniversalEquiv_tmul, DividedPowerAlgebra.map_apply_dp]
  simp only [Algebra.linearMap_apply, map_one, map_mul]
  rfl

end SerrePositivity.BhattScholze

end PrincipalDPBaseChangeUniversal

/-! ## 元のA→A/pに沿う実導来分冪表示環比較 -/

@[expose] public noncomputable section PrincipalDPRelativeDerivedModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実係数拡大の通常加群は、任意係数への既存表示環同型で具体的に計算できる。 -/
def principalDPRelativeModPScalarEquiv :
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of A R₀)) ≃ₗ[Q₀]
      PrincipalDPPresentation Q₀ (q₀ y) :=
  (principalDPBaseChangeUniversalEquiv (B := Q₀) y).toLinearEquiv

variable [Fact p.Prime]

/-- 正則入力では、元のA→A/pへの表示環の全高次Torは零。A平坦性は仮定しない。 -/
theorem principalDPRelativeModP_torVanishing
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    scalarExtensionTorVanishing q₀ (ModuleCat.of A R₀) := by
  change (∀ n : ℕ, 0 < n → IsZero
    (((Tor (ModuleCat.{u} A) n).obj (baseChangeScalarModule q₀)).obj (ModuleCat.of A R₀)))
  rw [← derivedModuleBaseChange_negative_homology_vanishes_iff q₀ (ModuleCat.of A R₀)]
  intro n hn
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  let Y := (boundedAboveDerivedBaseChange q₀).obj X
  have hni : -(n : ℤ) ≠ 0 :=
    neg_ne_zero.mpr (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hn))
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) ≅
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
        ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
          (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).mapIso
      (principalDPRelativeDerivedModPRestrictedIso y hA hpA hy)
  have ht : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      ((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (R₀ ⧸ Ideal.span {(p : R₀)})))) :=
    derivedSingleHomology_isZero _ (-(n : ℤ)) hni
  have hs : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(n : ℤ))).obj
      (((boundedAboveDerivedRestrictScalars q₀).obj Y).obj)) := e.isZero_iff.mpr ht
  have hr := (derivedRestrictScalarsHomologyIso q₀ (-(n : ℤ))).app Y.obj
  have hs' : IsZero ((ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)) :=
    hr.isZero_iff.mp hs
  let : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj) :=
    ModuleCat.subsingleton_of_isZero (R := A) hs'
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj
      Y.obj) := ModuleCat.isZero_of_subsingleton
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).obj Y.obj)
  exact IsZero.of_iso hz
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Q₀) (-(n : ℤ))).mapIso
      (boundedAboveDerivedBaseChangeModuleIso q₀ (ModuleCat.of A R₀))).symm

/-- 元のA→A/pで実導来還元した表示環は、係数p商上の具体的表示環の次数零対象。 -/
def principalDPRelativeDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ _
      (principalDPRelativeModP_torVanishing y hA hpA hy) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (principalDPRelativeModPScalarEquiv y).toModuleIso

end SerrePositivity.BhattScholze

end PrincipalDPRelativeDerivedModP

/-! ## 元の係数環上の実導来完備化と具体的mod p表示環 -/

@[expose] public noncomputable section PrincipalDPRelativeCompletionModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- Aのp正則性の下、標準A導来完備化単位を実p還元した射は同型。 -/
theorem principalDPRelativeCompletionUnit_modP_isIso
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) :
    IsIso ((boundedAboveDerivedBaseChange q₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  have hr : IsSMulRegular A (p : A) := hpA
  let F (b : A) := IsIso ((boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {b}))).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))
  have h : F ((p : A) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletion_quotient_unit_isIso A (p : A) hr 1 X
  exact Eq.mp (congrArg F (_root_.pow_one (p : A))) h

variable [Fact p.Prime]

/-- A上の実導来完備化を実p還元すると、係数A/p上の具体的表示環の次数零対象になる。 -/
def principalDPRelativeCompletedDerivedModPIso
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation Q₀ (q₀ y))) := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  letI := principalDPRelativeCompletionUnit_modP_isIso y hpA
  exact (asIso ((boundedAboveDerivedBaseChange q₀).map
      ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X))).symm ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy

/-- 実mod p比較は、元のA上の標準導来完備化単位と両立する。 -/
theorem principalDPRelativeCompletedDerivedModPIso_unit
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y)) :
    (boundedAboveDerivedBaseChange q₀).map
        ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀))) ≫
      (principalDPRelativeCompletedDerivedModPIso y hA hpA hy).hom =
        (principalDPRelativeDerivedModPIso y hA hpA hy).hom := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A R₀)
  let f := (boundedAboveDerivedBaseChange q₀).map
    ((DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)).app X)
  let := principalDPRelativeCompletionUnit_modP_isIso y hpA
  change (asIso f).hom ≫ ((asIso f).symm ≪≫
    principalDPRelativeDerivedModPIso y hA hpA hy).hom = _
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end SerrePositivity.BhattScholze

end PrincipalDPRelativeCompletionModP

/-! ## 一元分冪表示環と係数環への実評価テンソル環 -/

@[expose] public noncomputable section PrincipalDPEvaluationTensor

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} [CommRing A]
attribute [local instance] rankOneDPPolynomialAlgebra
local notation "P₀" => Polynomial A
local notation "G₀" => DividedPowerAlgebra A A
local notation "I₀" y => Ideal.span {(Polynomial.X - Polynomial.C y : P₀)}

/-- 多項式一次商の既存同型を、指定した評価多項式作用に関する代数同型とする。 -/
def principalDPEvaluationPolynomialEquiv (y : A) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    (P₀ ⧸ I₀ y) ≃ₐ[P₀] A := by
  letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  exact { (Polynomial.quotientSpanXSubCAlgEquiv y).toRingEquiv with
    commutes' := fun f ↦ by
      change Polynomial.eval y f = Polynomial.aeval y f
      simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] }

/-- 多項式一次関係の分冪代数への実像は、既存の表示関係イデアル。 -/
theorem principalDPEvaluation_relationIdeal (y : A) :
    (I₀ y).map (algebraMap P₀ G₀) = principalDPRelationIdeal y := by
  rw [Ideal.map_span, Set.image_singleton, map_sub]
  change Ideal.span {rankOneDPPolynomialMap A Polynomial.X -
    rankOneDPPolynomialMap A (Polynomial.C y)} = _
  rw [rankOneDPPolynomialMap_X, rankOneDPPolynomialMap_C]
  rfl

/-- 表示環から、Xをyへ評価した実テンソル環への標準同型。 -/
def principalDPEvaluationTensorEquiv (y : A) :
    PrincipalDPPresentation A y ≃+* RankOneDPEvaluatedEnvelope A A y := by
  letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  exact (Ideal.quotEquivOfEq (principalDPEvaluation_relationIdeal y).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot G₀ (I₀ y)).toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : G₀ ≃ₐ[G₀] G₀)
        (principalDPEvaluationPolynomialEquiv y)).toRingEquiv)

/-- すべての分冪代数の商代表元は、その元と1の純テンソルへ写る。 -/
theorem principalDPEvaluationTensorEquiv_mk (y : A) (d : G₀) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (Ideal.Quotient.mk _ d) = d ⊗ₜ[P₀] (1 : A) := by
  let : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
  rw [principalDPEvaluationTensorEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk G₀ (I₀ y) d]
  simp only [AlgEquiv.coe_toRingEquiv, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- 全標準分冪生成元上の実評価テンソル比較式。 -/
theorem principalDPEvaluationTensorEquiv_generator (y : A) (n : ℕ) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (principalDPGenerator y n) =
      DividedPowerAlgebra.dp A n (1 : A) ⊗ₜ[P₀] (1 : A) :=
  principalDPEvaluationTensorEquiv_mk y _

/-- 全係数上の実評価テンソル比較式。 -/
theorem principalDPEvaluationTensorEquiv_coeff (y a : A) :
    letI : Algebra P₀ A := rankOneDPEvaluationAlgebra (A := A) y
    principalDPEvaluationTensorEquiv y (algebraMap A (PrincipalDPPresentation A y) a) =
      (algebraMap A G₀ a) ⊗ₜ[P₀] (1 : A) :=
  principalDPEvaluationTensorEquiv_mk y _

/-- 元の係数作用を保つ、表示環と実評価テンソル環のA代数同型。 -/
def principalDPEvaluationTensorAlgEquiv (y : A) :
    PrincipalDPPresentation A y ≃ₐ[A] RankOneDPEvaluatedEnvelope A A y :=
  { principalDPEvaluationTensorEquiv y with
    commutes' := fun a ↦ principalDPEvaluationTensorEquiv_coeff y a }

end SerrePositivity.BhattScholze

end PrincipalDPEvaluationTensor

/-! ## 標数pでの一元分冪表示環の通常の忠実平坦性 -/

@[expose] public noncomputable section PrincipalDPQuotientFlat

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] rankOneDPPolynomialAlgebra
variable {p : ℕ} {B : Type v} [CommRing B]

/-- 指定した元のp乗商から、一元分冪表示環への実環射。 -/
def principalDPQuotientMap (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    B ⧸ Ideal.span {y ^ p} →+* PrincipalDPPresentation B y :=
  (principalDPEvaluationTensorEquiv y).symm.toRingHom.comp
    (rankOneDPEvaluatedQuotientMap hpos hp y)

/-- 実商射は、全代表元を自然な表示環の係数へ送る。 -/
theorem principalDPQuotientMap_mk (hpos : 0 < p) (hp : (p : B) = 0) (y b : B) :
    principalDPQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
      algebraMap B (PrincipalDPPresentation B y) b := by
  apply (principalDPEvaluationTensorEquiv y).injective
  change principalDPEvaluationTensorEquiv y
    ((principalDPEvaluationTensorEquiv y).symm
      (rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b))) = _
  rw [RingEquiv.apply_symm_apply]
  change rankOneDPEvaluatedQuotientMap hpos hp y (Ideal.Quotient.mk _ b) =
    principalDPEvaluationTensorAlgEquiv y (algebraMap B (PrincipalDPPresentation B y) b)
  rw [(principalDPEvaluationTensorAlgEquiv y).commutes]
  let := rankOneDPEvaluatedQuotientAlgebra hpos hp y
  let := rankOneDPEvaluatedQuotient_isScalarTower hpos hp y
  change algebraMap (B ⧸ Ideal.span {y ^ p}) (RankOneDPEvaluatedEnvelope B B y)
    (algebraMap B (B ⧸ Ideal.span {y ^ p}) b) = _
  exact (IsScalarTower.algebraMap_apply B (B ⧸ Ideal.span {y ^ p})
    (RankOneDPEvaluatedEnvelope B B y) b).symm

/-- 実商射が指定する表示環の商上の代数構造。 -/
abbrev principalDPQuotientAlgebra (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    Algebra (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) :=
  (principalDPQuotientMap hpos hp y).toAlgebra

/-- 実評価テンソル同型は、指定したp乗商上の代数同型でもある。 -/
def principalDPQuotientTensorAlgEquiv (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    letI := rankOneDPEvaluatedQuotientAlgebra hpos hp y
    PrincipalDPPresentation B y ≃ₐ[B ⧸ Ideal.span {y ^ p}]
      RankOneDPEvaluatedEnvelope B B y := by
  letI := principalDPQuotientAlgebra hpos hp y
  letI := rankOneDPEvaluatedQuotientAlgebra hpos hp y
  exact { principalDPEvaluationTensorEquiv y with
    commutes' := fun q ↦ (principalDPEvaluationTensorEquiv y).apply_symm_apply _ }

/-- 標数pの任意の一元入力の表示環は、その元のp乗商上で忠実平坦。 -/
theorem principalDPQuotient_moduleFaithfullyFlat
    (hprime : p.Prime) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hprime.pos hp y
    Module.FaithfullyFlat (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotientAlgebra hprime.pos hp y
  let := rankOneDPEvaluatedQuotient_moduleFaithfullyFlat hprime hp y
  exact Module.FaithfullyFlat.of_linearEquiv (B ⧸ Ideal.span {y ^ p})
    (RankOneDPEvaluatedEnvelope B B y)
    (principalDPQuotientTensorAlgEquiv hprime.pos hp y).toLinearEquiv

/-- 元のB係数作用と実p乗商作用は、表示環上でスカラー塔をなす。 -/
theorem principalDPQuotient_isScalarTower (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    IsScalarTower B (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := B) (S := B ⧸ Ideal.span {y ^ p})
    (A := PrincipalDPPresentation B y)
  intro b
  exact (principalDPQuotientMap_mk hpos hp y b).symm

variable {A : Type u} [CommRing A] [Algebra A B]

/-- 任意の基底環Aの元の係数作用とも、実p乗商作用は整合する。 -/
theorem principalDPQuotient_isScalarTower_base
    (hpos : 0 < p) (hp : (p : B) = 0) (y : B) :
    letI := principalDPQuotientAlgebra hpos hp y
    IsScalarTower A (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hpos hp y
  apply IsScalarTower.of_algebraMap_eq (R := A) (S := B ⧸ Ideal.span {y ^ p})
    (A := PrincipalDPPresentation B y)
  intro a
  rw [IsScalarTower.algebraMap_apply A B (B ⧸ Ideal.span {y ^ p})]
  change algebraMap A (PrincipalDPPresentation B y) a =
    principalDPQuotientMap hpos hp y (Ideal.Quotient.mk _ (algebraMap A B a))
  rw [principalDPQuotientMap_mk, IsScalarTower.algebraMap_apply A B
    (PrincipalDPPresentation B y)]

/-- 標数pのBと任意の基底環Aに対し、自然な商B/(y^p)がA平坦なら表示環もA平坦。 -/
theorem principalDPPresentation_flat_of_quotient_flat
    (hprime : p.Prime) (hp : (p : B) = 0) (y : B)
    (hQ : Module.Flat A (B ⧸ Ideal.span {y ^ p})) :
    Module.Flat A (PrincipalDPPresentation B y) := by
  let := principalDPQuotientAlgebra hprime.pos hp y
  let := principalDPQuotient_isScalarTower_base (A := A) hprime.pos hp y
  let := principalDPQuotient_moduleFaithfullyFlat hprime hp y
  let := hQ
  exact Module.Flat.trans A (B ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation B y)

end SerrePositivity.BhattScholze

end PrincipalDPQuotientFlat

/-! ## 正則一元入力の階乗部分環から任意の分冪標的への普遍射

標的のpねじれを許し、標的のδ構造・p局所性・完備性は要求しない。
-/

@[expose] public noncomputable section RegularPrincipalDPUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (H : DividedPowers I) (hyB : algebraMap A B y ∈ I)
local notation "ys" => fun _ : Unit ↦ y
local notation "S₀" => pDivisionFactorialSubring p ys
local notation "J₀" => pDivisionFactorialIdeal p ys
local notation "HA" => pDivisionFactorialIdealDividedPowers hA D ys
local notation "base₀" => pDivisionFactorialBase p ys
local notation "γ" n => (Subtype.mk (pDivisionFactorialValue p ys () n)
  (pDivisionFactorialSubring_value_mem ys () n) : S₀)

/-- 正則一元入力の階乗部分環から任意の分冪標的への実環射。 -/
def regularPrincipalDPLift : S₀ →+* B :=
  (principalDPEval H y hyB).toRingHom.comp (principalDPFactorialEquiv hA hpA D y hy).symm.toRingHom

include hpA hy hyB

/-- 実普遍射は元のAからの基底射を延長する。 -/
theorem regularPrincipalDPLift_coeff (a : A) :
    regularPrincipalDPLift hA hpA D y hy H hyB (base₀ a) = algebraMap A B a := by
  change principalDPEval H y hyB
    ((principalDPFactorialEquiv hA hpA D y hy).symm (base₀ a)) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply]
  exact AlgHom.commutes (principalDPEval H y hyB) a

/-- 実普遍射は全階乗生成元を標的の指定した分冪値へ送る。 -/
theorem regularPrincipalDPLift_value (n : ℕ) :
    regularPrincipalDPLift hA hpA D y hy H hyB (γ n) = H.dpow n (algebraMap A B y) := by
  change principalDPEval H y hyB ((principalDPFactorialEquiv hA hpA D y hy).symm (γ n)) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply]
  exact principalDPEval_generator H y hyB n

/-- 標的のねじれを許しても、実普遍射は正次数イデアルと全分冪を保つ。 -/
theorem regularPrincipalDPLift_isDPMorphism :
    DividedPowers.IsDPMorphism HA H (regularPrincipalDPLift hA hpA D y hy H hyB) := by
  let F := regularPrincipalDPLift hA hpA D y hy H hyB
  have hbase : base₀ y ∈ J₀ := pDivisionFactorialBase_mem_factorialIdeal ys ()
  have hγ : ∀ n : ℕ, (HA).dpow n (base₀ y) = γ n := by
    intro n
    apply Subtype.ext
    exact pDivisionFactorialIdealDividedPowers_base_apply hA D ys () n
  apply DividedPowers.IsDPMorphism.on_span HA H (S := Set.range (fun z : Unit × ℕ ↦
    (⟨pDivisionFactorialValue p ys z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem ys z.1 (z.2 + 1)⟩ : S₀))) rfl
  · rintro a ⟨⟨s, k⟩, rfl⟩
    cases s
    change F (γ (k + 1)) ∈ I
    rw [regularPrincipalDPLift_value]
    exact H.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n a ⟨⟨s, k⟩, rfl⟩
    cases s
    change F ((HA).dpow n (γ (k + 1))) = H.dpow n (F (γ (k + 1)))
    rw [← hγ (k + 1), (HA).dpow_comp (Nat.succ_ne_zero k) hbase, map_mul, map_natCast,
      hγ (n * (k + 1)), hγ (k + 1), regularPrincipalDPLift_value,
      regularPrincipalDPLift_value, H.dpow_comp (Nat.succ_ne_zero k) hyB]

/-- 基底射を延長する分冪射は、pねじれを許す任意の分冪標的に一意に存在する。 -/
theorem existsUnique_regularPrincipalDPMorphism :
    ∃! F : S₀ →+* B, F.comp base₀ = algebraMap A B ∧ DividedPowers.IsDPMorphism HA H F := by
  have hbaseF : (regularPrincipalDPLift hA hpA D y hy H hyB).comp base₀ = algebraMap A B := by
    ext a
    exact regularPrincipalDPLift_coeff hA hpA D y hy H hyB a
  refine ⟨regularPrincipalDPLift hA hpA D y hy H hyB,
    ⟨hbaseF, regularPrincipalDPLift_isDPMorphism hA hpA D y hy H hyB⟩, ?_⟩
  intro F hF
  apply pDivisionFactorialHom_ext ys
  · intro a
    exact (RingHom.congr_fun hF.1 a).trans (RingHom.congr_fun hbaseF a).symm
  · intro s n
    cases s
    have hγ : (HA).dpow n (base₀ y) = γ n := by
      apply Subtype.ext
      exact pDivisionFactorialIdealDividedPowers_base_apply hA D ys () n
    calc
      F (γ n) = F ((HA).dpow n (base₀ y)) := congrArg F hγ.symm
      _ = H.dpow n (F (base₀ y)) :=
        (hF.2.dpow_comp _ (pDivisionFactorialBase_mem_factorialIdeal ys ())).symm
      _ = H.dpow n (algebraMap A B y) := congrArg (H.dpow n) (RingHom.congr_fun hF.1 y)
      _ = _ := (regularPrincipalDPLift_value hA hpA D y hy H hyB n).symm

end SerrePositivity.BhattScholze

end RegularPrincipalDPUniversal

/-! ## 一元分冪表示環の実mod p比較

通常のp商を比較する。導来完備化や古典的完備化への置換は含まない。
-/

@[expose] public noncomputable section PrincipalDPModP

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} [CommRing A]
variable (p : ℕ) (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "I₀" => Ideal.span {(p : A)}
local notation "Q₀" => A ⧸ I₀
local notation "bar₀" => Ideal.Quotient.mk I₀

/-- 係数のp主イデアルの実表示環への像は、表示環内のp主イデアル。 -/
theorem principalDPModP_coefficientIdeal_map :
    (I₀).map (algebraMap A R₀) = Ideal.span {(p : R₀)} := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 一元分冪表示環の実p商と、係数環のp商上の実表示環の標準環同型（BS 著者版 Lemma 2.38 の一元の場合の mod p 底変換）。 -/
def principalDPModPEquiv :
    (R₀ ⧸ Ideal.span {(p : R₀)}) ≃+* PrincipalDPPresentation Q₀ (bar₀ y) :=
  (Ideal.quotEquivOfEq (principalDPModP_coefficientIdeal_map p y).symm).trans
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor R₀ I₀).toRingEquiv.trans
      (principalDPBaseChangeUniversalEquiv (B := Q₀) y).toRingEquiv)

/-- 実mod p同型は、すべての標準生成元の商像を対応する標準生成元へ送る。 -/
theorem principalDPModPEquiv_generator (n : ℕ) :
    principalDPModPEquiv p y (Ideal.Quotient.mk _ (principalDPGenerator y n)) =
      principalDPGenerator (bar₀ y) n := by
  rw [principalDPModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk R₀ I₀ (principalDPGenerator y n)]
  change principalDPBaseChangeUniversalEquiv (B := Q₀) y
    ((1 : Q₀) ⊗ₜ[A] principalDPGenerator y n) = _
  rw [principalDPBaseChangeUniversalEquiv_tmul_generator, map_one, one_mul]
  rfl

/-- 実mod p同型は、元の環の全係数の商像を対応する係数へ送る。 -/
theorem principalDPModPEquiv_coeff (a : A) :
    principalDPModPEquiv p y (Ideal.Quotient.mk _ (algebraMap A R₀ a)) =
      algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a) := by
  rw [principalDPModPEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply]
  erw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk R₀ I₀ (algebraMap A R₀ a)]
  change principalDPBaseChangeUniversalEquiv (B := Q₀) y
    ((1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a) = _
  have ha : (1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a = bar₀ a ⊗ₜ[A] (1 : R₀) := by
    change (1 : Q₀) ⊗ₜ[A] algebraMap A R₀ a = algebraMap A Q₀ a ⊗ₜ[A] (1 : R₀)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact (TensorProduct.tmul_smul (R := A) a (1 : Q₀) (1 : R₀)).trans
      (TensorProduct.smul_tmul' a (1 : Q₀) (1 : R₀))
  rw [ha, principalDPBaseChangeUniversalEquiv_coeff]
  rfl

end SerrePositivity.BhattScholze

end PrincipalDPModP

/-! ## 正則一元階乗部分環の実mod p比較 -/

@[expose] public noncomputable section RegularPrincipalDPModP

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)
local notation "R₀" => PrincipalDPPresentation A y
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "bar₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実表示環同型の逆により、階乗部分環のp主イデアルは表示環のp主イデアルへ写る。 -/
theorem regularPrincipalDPFactorialInverse_map_p :
    Ideal.span {(p : R₀)} = (Ideal.span {(p : S₀)}).map
      (principalDPFactorialEquiv hA hpA D y hy).symm.toRingHom := by
  rw [Ideal.map_span, Set.image_singleton, map_natCast]

/-- 具体的階乗部分環の実p商と、係数環のp商上の一元分冪表示環の環同型。 -/
def regularPrincipalDPFactorialModPEquiv :
    (S₀ ⧸ Ideal.span {(p : S₀)}) ≃+* PrincipalDPPresentation Q₀ (bar₀ y) :=
  (Ideal.quotientEquiv _ _ (principalDPFactorialEquiv hA hpA D y hy).symm
    (regularPrincipalDPFactorialInverse_map_p hA hpA D y hy)).trans (principalDPModPEquiv p y)

/-- 実mod p比較は、元の環の全基底係数の商像を対応する係数へ送る。 -/
theorem regularPrincipalDPFactorialModPEquiv_coeff (a : A) :
    regularPrincipalDPFactorialModPEquiv hA hpA D y hy
      (Ideal.Quotient.mk _ (pDivisionFactorialBase p (fun _ : Unit ↦ y) a)) =
      algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a) := by
  rw [regularPrincipalDPFactorialModPEquiv, RingEquiv.trans_apply]
  change principalDPModPEquiv p y (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
    ((principalDPFactorialEquiv hA hpA D y hy).symm
      (pDivisionFactorialBase p (fun _ : Unit ↦ y) a))) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply,
    principalDPModPEquiv_coeff]

/-- 実mod p比較は、全階乗生成元の商像を標準生成元へ送る。 -/
theorem regularPrincipalDPFactorialModPEquiv_generator (n : ℕ) :
    regularPrincipalDPFactorialModPEquiv hA hpA D y hy
      (Ideal.Quotient.mk _ (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀)) =
      principalDPGenerator (bar₀ y) n := by
  rw [regularPrincipalDPFactorialModPEquiv, RingEquiv.trans_apply]
  change principalDPModPEquiv p y (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
    ((principalDPFactorialEquiv hA hpA D y hy).symm
      (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
        pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀))) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply,
    principalDPModPEquiv_generator]

end SerrePositivity.BhattScholze

end RegularPrincipalDPModP

/-! ## 一元分冪表示環の実テンソル基底変更

通常の商環とテンソルの同型を既存APIから構成する。導来比較は含まない。
-/

@[expose] public noncomputable section PrincipalDPBaseChange

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

variable {p : ℕ} [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))

/-- 実テンソル同型による表示関係イデアルの像は、標的の表示関係イデアル。 -/
theorem principalDPBaseChange_relationIdeal (y : A) :
    principalDPRelationIdeal (algebraMap A B y) =
      ((principalDPRelationIdeal y).map
        (Algebra.TensorProduct.includeRight (R := A) (A := B)).toRingHom).map
          (rankOneDPBaseChangeEquiv hA hpA hB hpB).toRingHom :=
  principalDPBaseChangeUniversal_relationIdeal (B := B) y

/-- 一元分冪表示環は、p局所・p正則な係数環の基底変更と可換。 -/
def principalDPBaseChangeEquiv (y : A) :
    B ⊗[A] PrincipalDPPresentation A y ≃ₐ[B]
      PrincipalDPPresentation B (algebraMap A B y) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) B (DividedPowerAlgebra A A) B
    (principalDPRelationIdeal y)).trans
    (Ideal.quotientEquivAlg _ _ (rankOneDPBaseChangeEquiv hA hpA hB hpB)
      (principalDPBaseChange_relationIdeal hA hpA hB hpB y))

/-- 実商の基底変更同型はBの係数を保つ。 -/
theorem principalDPBaseChangeEquiv_coeff (y : A) (b : B) :
    principalDPBaseChangeEquiv hA hpA hB hpB y
      (b ⊗ₜ[A] (1 : PrincipalDPPresentation A y)) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b :=
  (principalDPBaseChangeEquiv hA hpA hB hpB y).commutes b

/-- 実商の基底変更同型の、標準生成元の全純テンソル上の式。 -/
theorem principalDPBaseChangeEquiv_tmul_generator (y : A) (b : B) (n : ℕ) :
    principalDPBaseChangeEquiv hA hpA hB hpB y (b ⊗ₜ[A] principalDPGenerator y n) =
      algebraMap B (PrincipalDPPresentation B (algebraMap A B y)) b *
        principalDPGenerator (algebraMap A B y) n :=
  principalDPBaseChangeUniversalEquiv_tmul_generator y b n

end SerrePositivity.BhattScholze

end PrincipalDPBaseChange

/-! ## 正則分冪表示環上の実導来完備化のmod p比較

表示環R自身上の単位加群を扱う。A上のRの平坦性は仮定しない。
-/

@[expose] public noncomputable section PrincipalDPCompletionModP

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A] (y : A)
local notation "R₀" => PrincipalDPPresentation A y
local notation "I₀" => Ideal.span {(p : R₀)}
local notation "Q₀" => R₀ ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀

/-- 表示環自身の単位加群には、p商への実係数拡大で高次Torは生じない。 -/
theorem principalDPUnitModP_torVanishing :
    scalarExtensionTorVanishing q₀ (ModuleCat.of R₀ R₀) := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
      exact ((MonoidalCategory.tensoringLeft (ModuleCat.{u} R₀)).obj
        (baseChangeScalarModule q₀)).isZero_leftDerived_obj_projective_succ n (ModuleCat.of R₀ R₀)

/-- 表示環の単位加群の実係数拡大は、実商環R/pの単位加群。 -/
def principalDPUnitModPScalarEquiv :
    ((ModuleCat.extendScalars q₀).obj (ModuleCat.of R₀ R₀)) ≃ₗ[Q₀] Q₀ := by
  let : Algebra R₀ Q₀ := (q₀).toAlgebra
  exact TensorProduct.AlgebraTensorModule.rid R₀ Q₀ Q₀

/-- 単位加群の実導来p還元は、標準augmentationにより実p商の次数零対象と一致する。 -/
def principalDPUnitDerivedModPIso :
    (boundedAboveDerivedBaseChange q₀).obj
        (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀)) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso _ _ (principalDPUnitModP_torVanishing y) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso (principalDPUnitModPScalarEquiv y).toModuleIso

variable [Fact p.Prime]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))

/-- 正則入力では、実導来p完備化の実導来p還元がR/pの次数零対象となる。 -/
def principalDPCompletedDerivedModPIso :
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Q₀) := by
  have hr : IsSMulRegular R₀ (p : R₀) := principalDPPresentation_p_mul_injective hA hpA y hy
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀)
  let F (b : R₀) :=
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj X ≅
      (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {b}))).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj X)
  have e : F ((p : R₀) ^ 1) :=
    DerivedCompletion.boundedAboveDerivedCompletionQuotientIso R₀ (p : R₀) hr 1 X
  have e' : F (p : R₀) := Eq.mp (congrArg F (_root_.pow_one (p : R₀))) e
  exact e'.symm ≪≫ principalDPUnitDerivedModPIso y

/-- 実導来完備化の実p還元は、既存の係数p商上の表示環にも具体的に同定される。 -/
def principalDPCompletedDerivedModPPresentationIso :
    letI := (principalDPModPEquiv p y).toRingHom.toAlgebra
    (boundedAboveDerivedBaseChange q₀).obj
        ((DerivedCompletion.boundedAboveDerivedCompletionFunctor R₀ (p : R₀)).obj
          (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R₀ R₀))) ≅
      boundedAboveDerivedSingleFunctor.obj
        (ModuleCat.of Q₀ (PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
          (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))) := by
  letI := (principalDPModPEquiv p y).toRingHom.toAlgebra
  let e : Q₀ ≃ₐ[Q₀] PrincipalDPPresentation (A ⧸ Ideal.span {(p : A)})
      (Ideal.Quotient.mk (Ideal.span {(p : A)}) y) :=
    { principalDPModPEquiv p y with commutes' := fun _ ↦ rfl }
  exact principalDPCompletedDerivedModPIso y hA hpA hy ≪≫
    boundedAboveDerivedSingleFunctor.mapIso e.toLinearEquiv.toModuleIso

end SerrePositivity.BhattScholze

end PrincipalDPCompletionModP

/-! ## 正則一元階乗部分環の実テンソル基底変更

具体的基底射による代数構造を明示する。通常の基底変更のみを扱う。
-/

@[expose] public noncomputable section RegularPrincipalDPBaseChange

namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
variable (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (y : A)
variable (hyA : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
variable (hyB : IsSMulRegular (B ⧸ Ideal.span {(p : B)})
  (Ideal.Quotient.mk (Ideal.span {(p : B)}) (algebraMap A B y)))
local notation "ysA" => fun _ : Unit ↦ y
local notation "ysB" => fun _ : Unit ↦ algebraMap A B y
local notation "SA" => pDivisionFactorialSubring p ysA
local notation "SB" => pDivisionFactorialSubring p ysB

/-- 正則一元階乗部分環の、指定された基底作用に関する実テンソル基底変更同型。 -/
def regularPrincipalDPBaseChangeEquiv :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    B ⊗[A] SA ≃ₐ[B] SB := by
  letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  let eA : PrincipalDPPresentation A y ≃ₐ[A] SA :=
    { __ := principalDPFactorialEquiv hA hpA D y hyA
      commutes' := principalDPFactorialEquiv_coeff hA hpA D y hyA }
  let eB : PrincipalDPPresentation B (algebraMap A B y) ≃ₐ[B] SB :=
    { __ := principalDPFactorialEquiv hB hpB E (algebraMap A B y) hyB
      commutes' := principalDPFactorialEquiv_coeff hB hpB E (algebraMap A B y) hyB }
  exact ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) eA).symm.trans
    (principalDPBaseChangeEquiv hA hpA hB hpB y)).trans eB

/-- 実基底変更同型は指定したBの係数を保つ。 -/
theorem regularPrincipalDPBaseChangeEquiv_coeff (b : B) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB (b ⊗ₜ[A] (1 : SA)) =
      pDivisionFactorialBase p ysB b := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  exact (regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB).commutes b

/-- 実基底変更同型の全階乗生成元の純テンソル上の具体式。 -/
theorem regularPrincipalDPBaseChangeEquiv_tmul_value (b : B) (n : ℕ) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB
      (b ⊗ₜ[A] (⟨pDivisionFactorialValue p ysA () n,
        pDivisionFactorialSubring_value_mem ysA () n⟩ : SA)) =
      pDivisionFactorialBase p ysB b *
        (⟨pDivisionFactorialValue p ysB () n,
          pDivisionFactorialSubring_value_mem ysB () n⟩ : SB) := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  dsimp only [regularPrincipalDPBaseChangeEquiv]
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_symm_apply,
    Algebra.TensorProduct.map_tmul]
  change principalDPFactorialEquiv hB hpB E (algebraMap A B y) hyB
    (principalDPBaseChangeEquiv hA hpA hB hpB y
      (b ⊗ₜ[A] (principalDPFactorialEquiv hA hpA D y hyA).symm
        ⟨pDivisionFactorialValue p ysA () n,
          pDivisionFactorialSubring_value_mem ysA () n⟩)) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hyA n, RingEquiv.symm_apply_apply,
    principalDPBaseChangeEquiv_tmul_generator, map_mul,
    principalDPFactorialEquiv_coeff, principalDPFactorialEquiv_generator]


/-- 実基底変更同型の全純テンソル上の式は、既存の具体的部分環射で与えられる。 -/
theorem regularPrincipalDPBaseChangeEquiv_tmul (b : B) (a : SA) :
    letI : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
    letI : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
    regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB (b ⊗ₜ[A] a) =
      pDivisionFactorialBase p ysB b * pDivisionFactorialMap hA (algebraMap A B) ysA a := by
  let : Algebra A SA := (pDivisionFactorialBase p ysA).toAlgebra
  let : Algebra B SB := (pDivisionFactorialBase p ysB).toAlgebra
  let e := regularPrincipalDPBaseChangeEquiv hA hpA hB hpB D E y hyA hyB
  have hmap : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := SA)).toRingHom =
      pDivisionFactorialMap hA (algebraMap A B) ysA := by
    apply pDivisionFactorialHom_ext ysA
    · intro r
      change e ((1 : B) ⊗ₜ[A] pDivisionFactorialBase p ysA r) = _
      have hr : (1 : B) ⊗ₜ[A] pDivisionFactorialBase p ysA r =
          algebraMap A B r ⊗ₜ[A] (1 : SA) := by
        change (1 : B) ⊗ₜ[A] algebraMap A SA r = algebraMap A B r ⊗ₜ[A] (1 : SA)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        exact (TensorProduct.tmul_smul (R := A) r (1 : B) (1 : SA)).trans
          (TensorProduct.smul_tmul' r (1 : B) (1 : SA))
      rw [hr, regularPrincipalDPBaseChangeEquiv_coeff]
      exact (RingHom.congr_fun (pDivisionFactorialMap_comp_base hA (algebraMap A B) ysA) r).symm
    · intro s n
      cases s
      change e ((1 : B) ⊗ₜ[A] (⟨pDivisionFactorialValue p ysA () n,
        pDivisionFactorialSubring_value_mem ysA () n⟩ : SA)) = _
      rw [regularPrincipalDPBaseChangeEquiv_tmul_value, pDivisionFactorialMap_value,
        map_one, one_mul]
  have ht : b ⊗ₜ[A] a = (b ⊗ₜ[A] (1 : SA)) * ((1 : B) ⊗ₜ[A] a) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul, regularPrincipalDPBaseChangeEquiv_coeff]
  exact congrArg (fun t : SB ↦ pDivisionFactorialBase p ysB b * t)
    (RingHom.congr_fun hmap a)

end SerrePositivity.BhattScholze

end RegularPrincipalDPBaseChange

/-! ## 正則階乗部分環の実mod p商の通常平坦性 -/

@[expose] public noncomputable section RegularPrincipalDPModPFlat

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)
local notation "Q₀" => A ⧸ Ideal.span {(p : A)}
local notation "T₀" => S₀ ⧸ Ideal.span {(p : S₀)}
local notation "bar₀" => Ideal.Quotient.mk (Ideal.span {(p : A)})

/-- 実比較同型を通じて指定した、階乗部分環の実p商の係数環A/p作用。 -/
abbrev regularPrincipalDPModPCoefficientAlgebra : Algebra Q₀ T₀ :=
  ((regularPrincipalDPFactorialModPEquiv hA hpA D y hy).symm.toRingHom.comp
    (algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)))).toAlgebra

set_option maxRecDepth 2048 in
/-- 指定したA/p作用は、元の環の全係数上で階乗部分環の実基底射のp商と一致する。 -/
theorem regularPrincipalDPModPCoefficientAlgebra_mk (a : A) :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    algebraMap Q₀ T₀ (bar₀ a) =
      Ideal.Quotient.mk _ (pDivisionFactorialBase p (fun _ : Unit ↦ y) a) := by
  let := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  apply (regularPrincipalDPFactorialModPEquiv hA hpA D y hy).injective
  change regularPrincipalDPFactorialModPEquiv hA hpA D y hy
    ((regularPrincipalDPFactorialModPEquiv hA hpA D y hy).symm
      (algebraMap Q₀ (PrincipalDPPresentation Q₀ (bar₀ y)) (bar₀ a))) = _
  rw [RingEquiv.apply_symm_apply, regularPrincipalDPFactorialModPEquiv_coeff]

/-- 実p商の比較は、明示した自然係数作用に関するA/p代数同型。 -/
def regularPrincipalDPModPAlgEquiv :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    T₀ ≃ₐ[Q₀] PrincipalDPPresentation Q₀ (bar₀ y) := by
  letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  exact { regularPrincipalDPFactorialModPEquiv hA hpA D y hy with
    commutes' := fun _ ↦ (regularPrincipalDPFactorialModPEquiv hA hpA D y hy).apply_symm_apply _ }

/-- 任意のK→A/p作用に対し、p乗商のK平坦性から実階乗部分環のp商のK平坦性を得る。 -/
theorem regularPrincipalDPModP_flat_of_powerQuotient_flat
    {K : Type v} [CommRing K] [Algebra K Q₀]
    (hQ : Module.Flat K (Q₀ ⧸ Ideal.span {(bar₀ y) ^ p})) :
    letI := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
    letI : Algebra K T₀ := Algebra.compHom T₀ (algebraMap K Q₀)
    Module.Flat K T₀ := by
  let := regularPrincipalDPModPCoefficientAlgebra hA hpA D y hy
  let : Algebra K T₀ := Algebra.compHom T₀ (algebraMap K Q₀)
  let : IsScalarTower K Q₀ T₀ := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hp : (p : Q₀) = 0 := by
    change Ideal.Quotient.mk _ (p : A) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  let := principalDPPresentation_flat_of_quotient_flat (Fact.out : p.Prime) hp (bar₀ y) hQ
  exact Module.Flat.of_linearEquiv
    ((regularPrincipalDPModPAlgEquiv hA hpA D y hy).restrictScalars K).toLinearEquiv

end SerrePositivity.BhattScholze

end RegularPrincipalDPModPFlat
