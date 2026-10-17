module

public import SerrePositivity.BhattScholze.Andre.DividedPowerPrimeUniversal

/-!
# André E1・E2：一次関係商と係数 p 乗商上の切断表示

## 概要

一元分冪代数に γ₁=y を課した表示環を、A/(yᵖ) 上の可算切断多項式商と比較する。
BS Rem 7.15(1)（著者版 p.62）の明示的な通常環表示。

## 方針

最初の切断変数を y の係数像、後続の変数を残りの切断変数へ送る。
逆向きは後続の素数冪分冪を使う。

## 規約

p は素数で A 内で零。ここで扱うのは一次関係を課した通常環であり、
実 pd 包の分冪構造・普遍性との比較は別工程である。

## 使われ方

原典の A/(yᵖ)[g₁,g₂,…]/(gᵢᵖ) という自由な表示を具体化する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (p : ℕ) [Fact p.Prime]
local notation "hprime" => (Fact.out : p.Prime)

/-- 概要：係数 y の p 乗商上の可算切断多項式表示環。
方針：既存の切断多項式商の係数環を実商 A/(yᵖ) にする。
規約：変数 i は元の分冪の次数 p^(i+1) に対応する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示表示の右辺。 -/
abbrev PrincipalDPTruncatedPresentation (y : A) :=
  DividedPowerPrimeTruncatedAlgebra (A := A ⧸ Ideal.span {y ^ p}) p

/-- 概要：係数 y と後続の切断変数からなる可算元族。
方針：零番目に係数 y の像、後続に通常の切断変数を置く。
規約：番号を一つずらして一次分冪の関係を取り出す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係を満たす評価。 -/
def principalDPTruncatedRoot (y : A) : ℕ → PrincipalDPTruncatedPresentation p y
  | 0 => algebraMap A _ y
  | i + 1 => Ideal.Quotient.mk _ (MvPolynomial.X i)

omit [Fact p.Prime] in
/-- 概要：係数 y と後続の切断変数はいずれも p 乗が零。
方針：零番目には係数商の関係、後続には切断変数の関係を使う。
規約：係数環の非零性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の普遍評価射の入力。 -/
theorem principalDPTruncatedRoot_pow (y : A) (i : ℕ) :
    principalDPTruncatedRoot p y i ^ p = 0 := by
  cases i with
  | zero =>
    change Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {y ^ p}) y)) ^ p = 0
    rw [← map_pow, ← map_pow, ← map_pow]
    have hy : Ideal.Quotient.mk (Ideal.span {y ^ p}) (y ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hy, map_zero, map_zero]
  | succ i =>
    exact (monicPowerFamilyQuotient_root_pow p ℕ (A ⧸ Ideal.span {y ^ p})
      (fun _ => 0) i).trans (map_zero _)

/-- 概要：自由分冪代数から係数 p 乗商上の切断表示への標準射。
方針：可算切断表示の逆同型と、指定した p 乗零元族への普遍評価を合成する。
規約：最初の素数冪分冪は係数 y へ送る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の一次関係商の順射。 -/
def principalDPToTruncatedRaw (hp : (p : A) = 0) (y : A) :
    DividedPowerAlgebra A A →ₐ[A] PrincipalDPTruncatedPresentation p y :=
  (dividedPowerPrimeTruncatedLift (A := A) p (principalDPTruncatedRoot p y)
    (principalDPTruncatedRoot_pow p y)).comp (dividedPowerPrimeTruncatedEquiv p hp).symm.toAlgHom

/-- 概要：自由分冪からの射は素数冪分冪を指定した係数・変数族へ送る。
方針：切断表示同型の逆と変数上の普遍評価を使う。
規約：次数は p の自然数冪。
使われ方：BS Rem 7.15(1)（著者版 p.62）の二射の比較。 -/
theorem principalDPToTruncatedRaw_dp (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPToTruncatedRaw p hp y (DividedPowerAlgebra.dp A (p ^ i) (1 : A)) =
      principalDPTruncatedRoot p y i := by
  rw [← dividedPowerPrimeTruncatedEquiv_X p hp i]
  change dividedPowerPrimeTruncatedLift (A := A) p (principalDPTruncatedRoot p y)
    (principalDPTruncatedRoot_pow p y)
    ((dividedPowerPrimeTruncatedEquiv p hp).symm
      (dividedPowerPrimeTruncatedEquiv p hp (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = _
  rw [AlgEquiv.symm_apply_apply]
  exact dividedPowerPrimeTruncatedLift_X p _ (principalDPTruncatedRoot_pow p y) i

/-- 概要：一次関係商から係数 p 乗商上の切断表示への標準射。
方針：一次分冪を y に送ることを使い、自由分冪代数からの射を商に降ろす。
規約：係数環 A の作用を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の順射。 -/
def principalDPToTruncated (hp : (p : A) = 0) (y : A) :
    PrincipalDPPresentation A y →ₐ[A] PrincipalDPTruncatedPresentation p y := by
  apply Ideal.Quotient.liftₐ _ (principalDPToTruncatedRaw p hp y)
  have hker : principalDPRelationIdeal y ≤ RingHom.ker (principalDPToTruncatedRaw p hp y) := by
    apply Ideal.span_le.mpr
    rintro _ (rfl : _ = _)
    change principalDPToTruncatedRaw p hp y
      (DividedPowerAlgebra.dp A 1 (1 : A) - algebraMap A _ y) = 0
    rw [map_sub, show (1 : ℕ) = p ^ 0 by simp, principalDPToTruncatedRaw_dp, AlgHom.commutes]
    exact sub_self _
  exact fun _ hx => hker hx

/-- 概要：一次関係商の素数冪分冪の標準像を指定した元族へ送る。
方針：商への降下前の評価公式を使う。
規約：零番目の値は係数 y である。
使われ方：BS Rem 7.15(1)（著者版 p.62）の逆合成の確認。 -/
theorem principalDPToTruncated_generator (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPToTruncated p hp y (principalDPGenerator y (p ^ i)) =
      principalDPTruncatedRoot p y i :=
  principalDPToTruncatedRaw_dp p hp y i

/-- 概要：一次関係商の全素数冪分冪生成元は p 乗が零。
方針：自由分冪代数の消滅式を商射で移す。
規約：入力 y の正則性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の切断商の普遍射の入力。 -/
theorem principalDPPrimeGenerator_pow_zero (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPGenerator y (p ^ i) ^ p = 0 := by
  change (Ideal.Quotient.mk (principalDPRelationIdeal y)
    (DividedPowerAlgebra.dp A (p ^ i) (1 : A))) ^ p = 0
  rw [← map_pow, dividedPowerPrimePower_pow_zero p hp, map_zero]

/-- 概要：係数 p 乗商上の切断表示から一次関係商への標準射。
方針：既存の係数商作用を使い、変数 i を次数 p^(i+1) の分冪の像に送る。
規約：元の A 作用とのスカラー塔を明示してから制限する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の表示同型の逆射。 -/
def principalDPTruncatedToPresentation (hp : (p : A) = 0) (y : A) :
    PrincipalDPTruncatedPresentation p y →ₐ[A] PrincipalDPPresentation A y := by
  letI := principalDPQuotientAlgebra (hprime).pos hp y
  letI := principalDPQuotient_isScalarTower (hprime).pos hp y
  exact (dividedPowerPrimeTruncatedLift (A := A ⧸ Ideal.span {y ^ p}) p
    (fun i => principalDPGenerator y (p ^ (i + 1)))
    (fun i => principalDPPrimeGenerator_pow_zero p hp y (i + 1))).restrictScalars A

/-- 概要：逆向きの標準射は変数 i を次数 p^(i+1) の分冪の像へ送る。
方針：切断商の普遍射の変数公式を使う。
規約：最初の変数は次数 p の分冪を表す。
使われ方：BS Rem 7.15(1)（著者版 p.62）の逆合成の検証。 -/
theorem principalDPTruncatedToPresentation_X (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPTruncatedToPresentation p hp y (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      principalDPGenerator y (p ^ (i + 1)) := by
  let := principalDPQuotientAlgebra (hprime).pos hp y
  let := principalDPQuotient_isScalarTower (hprime).pos hp y
  exact dividedPowerPrimeTruncatedLift_X (A := A ⧸ Ideal.span {y ^ p}) p
    (fun i => principalDPGenerator y (p ^ (i + 1)))
    (fun i => principalDPPrimeGenerator_pow_zero p hp y (i + 1)) i


omit [Fact p.Prime] in
/-- 概要：係数 p 乗商上の切断表示からの A 代数射は変数の値で決まる。
方針：係数商の各元を A から持ち上げ、係数上は代数射の可換性を使う。
規約：終域に係数商上の代数構造は要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の二射の逆合成の検証。 -/
theorem principalDPTruncatedHom_ext {B : Type u} [CommRing B] [Algebra A B] (y : A)
    (f g : PrincipalDPTruncatedPresentation p y →ₐ[A] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply AlgHom.toRingHom_injective
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    change f (algebraMap A _ a) = g (algebraMap A _ a)
    exact (f.commutes a).trans (g.commutes a).symm
  · exact h

/-- 概要：一次関係商から切断表示へ移して戻すと恒等射になる。
方針：素数冪分冪の像で比較し、次数一では一次関係、後続では変数公式を使う。
規約：係数環の非零性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示表示同型の検証。 -/
theorem principalDPTruncatedToPresentation_comp_toTruncated (hp : (p : A) = 0) (y : A) :
    (principalDPTruncatedToPresentation p hp y).comp (principalDPToTruncated p hp y) =
      AlgHom.id A _ := by
  apply principalDPPrimeHom_ext p hp y
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply, principalDPToTruncated_generator]
  cases i with
  | zero =>
    change principalDPTruncatedToPresentation p hp y (algebraMap A _ y) =
      principalDPGenerator y 1
    rw [AlgHom.commutes, principalDPGenerator_one]
  | succ i => exact principalDPTruncatedToPresentation_X p hp y i

/-- 概要：切断表示から一次関係商へ移して戻しても恒等射になる。
方針：切断変数上の外延性と両方向の生成元の公式を使う。
規約：元の A 係数作用を保つ射として述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示表示同型の検証。 -/
theorem principalDPToTruncated_comp_truncatedToPresentation (hp : (p : A) = 0) (y : A) :
    (principalDPToTruncated p hp y).comp (principalDPTruncatedToPresentation p hp y) =
      AlgHom.id A _ := by
  apply principalDPTruncatedHom_ext
  intro i
  change principalDPToTruncated p hp y
    (principalDPTruncatedToPresentation p hp y (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
  rw [principalDPTruncatedToPresentation_X, principalDPToTruncated_generator]
  rfl

/-- 概要：γ₁=y の一元分冪表示環は係数商 A/(yᵖ) 上の可算切断表示と A 代数同型。
方針：素数冪分冪と切断変数で照合した互いに逆な二射を束ねる。
規約：実 pd 包との同定はこの通常代数同型に含まない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示的な自由表示。 -/
def principalDPTruncatedEquiv (hp : (p : A) = 0) (y : A) :
    PrincipalDPPresentation A y ≃ₐ[A] PrincipalDPTruncatedPresentation p y :=
  AlgEquiv.ofAlgHom (principalDPToTruncated p hp y) (principalDPTruncatedToPresentation p hp y)
    (principalDPToTruncated_comp_truncatedToPresentation p hp y)
    (principalDPTruncatedToPresentation_comp_toTruncated p hp y)

/-- 概要：表示同型は次数 p^(i+1) の分冪の標準像を i 番目の切断変数へ送る。
方針：同型の順射の生成元公式を使う。
規約：一次分冪は係数に移り、変数は次の素数冪から始まる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の原典の g₁,g₂,… との対応。 -/
theorem principalDPTruncatedEquiv_generator_succ (hp : (p : A) = 0) (y : A) (i : ℕ) :
    principalDPTruncatedEquiv p hp y (principalDPGenerator y (p ^ (i + 1))) =
      Ideal.Quotient.mk _ (MvPolynomial.X i) :=
  principalDPToTruncated_generator p hp y (i + 1)


/-- 概要：一次関係商と切断表示の同型は既存の係数商 A/(yᵖ) 作用を保つ。
方針：係数商の代表元を A から持ち上げ、標準係数商射の値と A 代数同型の可換性を使う。
規約：一次関係商側の作用は既存の principalDPQuotientAlgebra をそのまま使う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数商からの自由拡大の表示。 -/
def principalDPTruncatedQuotientAlgEquiv (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (hprime).pos hp y
    PrincipalDPPresentation A y ≃ₐ[A ⧸ Ideal.span {y ^ p}]
      PrincipalDPTruncatedPresentation p y := by
  letI := principalDPQuotientAlgebra (hprime).pos hp y
  refine { (principalDPTruncatedEquiv p hp y).toRingEquiv with commutes' := ?_ }
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  change principalDPTruncatedEquiv p hp y
    (principalDPQuotientMap (hprime).pos hp y (Ideal.Quotient.mk _ a)) = algebraMap A _ a
  rw [principalDPQuotientMap_mk]
  exact (principalDPTruncatedEquiv p hp y).commutes a


/-- 概要：係数 p 乗商上の可算切断表示はその係数環上自由。
方針：既存のモニック冪関係商と通常根添加環の同型で自由性を移す。
規約：零係数商を含み、y の正則性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示表示の自由性。 -/
theorem principalDPTruncatedPresentation_free (y : A) :
    Module.Free (A ⧸ Ideal.span {y ^ p}) (PrincipalDPTruncatedPresentation p y) := by
  let B := A ⧸ Ideal.span {y ^ p}
  let := monicPowerFamilyCover_moduleFree p ℕ B (fun _ => 0) (hprime).pos
  exact Module.Free.of_equiv
    (monicPowerFamilyPresentationAlgEquiv p ℕ B (fun _ => 0)).symm.toLinearEquiv

/-- 概要：一次関係商は既存の係数商 A/(yᵖ) 作用について自由。
方針：具体的切断表示の自由性を係数商上の代数同型で戻す。
規約：作用は既存の principalDPQuotientAlgebra を固定し、補助平坦性を仮定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の明示表示による自由性の証明。 -/
theorem principalDPPresentation_free_via_truncated (hp : (p : A) = 0) (y : A) :
    letI := principalDPQuotientAlgebra (hprime).pos hp y
    Module.Free (A ⧸ Ideal.span {y ^ p}) (PrincipalDPPresentation A y) := by
  let := principalDPQuotientAlgebra (hprime).pos hp y
  let := principalDPTruncatedPresentation_free p y
  exact Module.Free.of_equiv (principalDPTruncatedQuotientAlgEquiv p hp y).symm.toLinearEquiv

end SerrePositivity.BhattScholze.Andre
