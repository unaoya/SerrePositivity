module
public meta import SerrePositivity.Util.Citation
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialSubring
public import SerrePositivity.CommutativeAlgebra.DividedPowers.FactorialCoefficients

public import SerrePositivity.BhattScholze.Delta.Division.Relations
public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import SerrePositivity.BhattScholze.Delta.Division.Basic
public import SerrePositivity.BhattScholze.Delta.DividedPower.Coefficients.Factorial
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaRing
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
public import Mathlib.RingTheory.WittVector.Identities
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWitt
public import Mathlib.RingTheory.Regular.Flat

/-!
# A{φ(y)/p} と階乗生成部分環（BS 著者版 Lemma 2.36）

## 概要
p 除算添加環の p 局所化、A[1/p] の中の階乗分母生成部分環と raw δ 評価の像、その δ 安定性・δ 構造・分冪作用、raw 包の像の最小性、正次数の階乗分母の生成イデアルの分冪構造、写像の関手性・一意性、p 正則な分冪標的への延長と普遍性、最初の p 除算関係の正則性、q(y)=0 となる係数射に沿う Witt 解と raw 包からの環射。
像の δ 構造からの独立性と最初の関係式の Koszul 分解は、BS 著者版 Lemma 2.36 と Remark 2.37 の押し出しの計算に関わる補助である。

## 方針
原典の BS 著者版 Lemma 2.36 を、任意の p 局所 δ 環と元族について A[1/p] の中の像の形で述べる（生の pushout が p ねじれなしであることは r = 1 で `Andre/Envelope/PDivision` にある）。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Andre/Envelope/PDivision`、`Andre/PowerRootEnvelope/DeltaDivisionWitt`、`Delta/DividedPower/PrincipalDP`。
-/

universe u v w z

/-! ## 最初の実p除算関係と通常商のp正則性

任意の指定変数sについて、δ閉包前の一つの実関係式を扱う。
全δ関係商・完備化・分冪包の平坦性は結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionFirstRelationRegular

set_option backward.isDefEq.respectTransparency false
open scoped Pointwise
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "g₀" => deltaDivisionIteratedRelation D (p : A) (fun t ↦ D.frobeniusLift (y t)) s 0
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : L₀)})

/-- 最初の実p除算関係のmod p像は指定元の係数像のp乗の負。 -/
theorem deltaPDivisionFirstRelation_mod_p :
    q₀ g₀ = -(q₀ (MvPolynomial.C (y s))) ^ p := by
  have hp : q₀ (MvPolynomial.C (p : A)) = 0 := by
    rw [map_natCast (MvPolynomial.C : A →+* L₀) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
    MvPolynomial.C (D.frobeniusLift (y s))) = _
  rw [map_sub, map_mul, hp, zero_mul, zero_sub, D.frobeniusLift_apply,
    map_add, map_pow, map_mul, map_add, map_pow, map_mul, hp, zero_mul, add_zero]

variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) (y s)))

include hpA hy

/-- y_sが係数環のmod pで正則なら、実最初のp除算関係もL/pで正則。 -/
theorem deltaPDivisionFirstRelation_mod_p_isSMulRegular :
    IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)}) (q₀ g₀) := by
  let qA := Ideal.Quotient.mk (Ideal.span {(p : A)})
  have hφ : IsSMulRegular (A ⧸ Ideal.span {(p : A)} ) (qA (D.frobeniusLift (y s))) := by
    have hp : qA (p : A) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self _)
    have he : qA (D.frobeniusLift (y s)) = qA (y s) ^ p := by
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp, zero_mul, add_zero]
    rw [he]
    exact hy.pow p
  have hc := SerrePositivity.isSMulRegular_mod_of_flat (S := L₀)
    (p : A) (D.frobeniusLift (y s)) hpA hφ
  have hc' : IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)})
      (q₀ (MvPolynomial.C (D.frobeniusLift (y s)))) := by
    have aux (c : L₀) (he : c = (p : L₀))
        (h : IsSMulRegular (L₀ ⧸ Ideal.span {c})
          (Ideal.Quotient.mk (Ideal.span {c}) (MvPolynomial.C (D.frobeniusLift (y s))))) :
        IsSMulRegular (L₀ ⧸ Ideal.span {(p : L₀)})
          (q₀ (MvPolynomial.C (D.frobeniusLift (y s)))) := by
      subst c
      exact h
    exact aux _ (map_natCast (algebraMap A L₀) p) hc
  have he : q₀ g₀ = -q₀ (MvPolynomial.C (D.frobeniusLift (y s))) := by
    change q₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s))) = _
    rw [map_sub, map_mul, map_natCast (MvPolynomial.C : A →+* L₀) p,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (p : L₀)),
      zero_mul, zero_sub]
  rw [he]
  intro x z hxz
  apply hc'
  simpa only [neg_smul, neg_inj] using hxz

/-- δ閉包前の実最初の関係商には新しいpねじれが生じない。 -/
theorem deltaPDivisionFirstRelation_quotient_p_mul_injective :
    Function.Injective (fun x : L₀ ⧸ Ideal.span {g₀} ↦ (p : L₀ ⧸ Ideal.span {g₀}) * x) := by
  have hpL : IsSMulRegular L₀ (p : L₀) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    simpa only [map_natCast] using h
  have h := SerrePositivity.isSMulRegular_quotient_span_of_regular_mod L₀ (p : L₀) g₀ hpL
    (deltaPDivisionFirstRelation_mod_p_isSMulRegular D y s hpA hy)
  exact Eq.mp (congrArg (fun c : L₀ ⧸ Ideal.span {g₀} ↦
    IsSMulRegular (L₀ ⧸ Ideal.span {g₀}) c)
      (map_natCast (Ideal.Quotient.mk (Ideal.span {g₀})) p)) h

/-- pと最初の実p除算関係は自由環上の弱正則対。 -/
theorem deltaPDivisionFirstRelation_pair_isWeaklyRegular :
    RingTheory.Sequence.IsWeaklyRegular L₀ [(p : L₀), g₀] := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨?_, ?_⟩
  · have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    simpa only [map_natCast] using h
  · let e := Submodule.quotEquivOfEq
      ((p : L₀) • (⊤ : Submodule L₀ L₀))
      (Ideal.span {(p : L₀)} : Submodule L₀ L₀)
      (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])
    apply (e.isSMulRegular_congr _).mpr
    exact (isSMulRegular_map (Ideal.Quotient.mk _) (fun _ ↦ rfl)).mp
      (deltaPDivisionFirstRelation_mod_p_isSMulRegular D y s hpA hy)

/-- 実対(p,g_s)のKoszul複体は対応する通常商の分解。 -/
theorem deltaPDivisionFirstRelation_pair_isKoszulResolution :
    SerrePositivity.IsKoszulResolution
      (fun i : Fin 2 ↦ if i = 0 then (p : L₀) else g₀) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa [List.ofFn_succ] using deltaPDivisionFirstRelation_pair_isWeaklyRegular D y s hpA hy

end SerrePositivity.BhattScholze

end DeltaPDivisionFirstRelationRegular

/-! ## p除算添加環のp局所化

任意元族について、A{a_s/p}[1/p]をA[1/p]と具体的δ環同型で比較する。
正則性・有限性・完備性は要求しない。
-/

@[expose] public noncomputable section DeltaPDivisionLocalization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (a : σ → A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a
local notation "Aₚ" => Localization.Away (p : A)
local notation "Bₚ" => Localization.Away (p : B₀)

/-- p冪局所化上の既存δ構造の具体的特殊化。 -/
abbrev deltaPDivisionAwayStructure : DeltaStructure p Aₚ :=
  D.localization (Submonoid.powers (p : A)) Aₚ D.powers_p_frobenius_stable

/-- 元の環からp局所化への標準射はδ射。 -/
theorem deltaPDivisionAwayStructure_base_isDeltaHom :
    D.IsDeltaHom (deltaPDivisionAwayStructure D) (algebraMap A Aₚ) :=
  D.isDeltaHom_localization (Submonoid.powers (p : A)) Aₚ D.powers_p_frobenius_stable

/-- 各除算変数をa_s/pへ送るδ射が一意に存在する。 -/
theorem existsUnique_deltaPDivisionToAway :
    ∃! f : B₀ →+* Aₚ, (E₀).IsDeltaHom (deltaPDivisionAwayStructure D) f ∧
      f.comp j₀ = algebraMap A Aₚ ∧ ∀ s,
        f (deltaAdjoinDivisionVariable D (p : A) a s) =
          IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s) := by
  apply existsUnique_deltaAdjoinDivisionHom D (deltaPDivisionAwayStructure D) (p : A) a
    (algebraMap A Aₚ) (deltaPDivisionAwayStructure_base_isDeltaHom D)
    (fun s ↦ IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s))
  intro s
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf, one_mul]

/-- raw p除算添加環からA[1/p]への具体的δ射。 -/
def deltaPDivisionToAway : B₀ →+* Aₚ := (existsUnique_deltaPDivisionToAway D a).choose

/-- 具体的δ射のδ・基底・除算変数上の式。 -/
theorem deltaPDivisionToAway_spec :
    (E₀).IsDeltaHom (deltaPDivisionAwayStructure D) (deltaPDivisionToAway D a) ∧
      (deltaPDivisionToAway D a).comp j₀ = algebraMap A Aₚ ∧ ∀ s,
        deltaPDivisionToAway D a (deltaAdjoinDivisionVariable D (p : A) a s) =
          IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (a s) :=
  (existsUnique_deltaPDivisionToAway D a).choose_spec.1

omit [Fact p.Prime] in
private theorem map_powers_isUnit {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (h : IsUnit (f (p : R))) (s : Submonoid.powers (p : R)) : IsUnit (f s) := by
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) (p : R)).mp s.property
  rw [← hn, map_pow]
  exact h.pow n

/-- A[1/p]からp除算添加環のp局所化へのδ延長が一意に存在する。 -/
theorem existsUnique_deltaPDivisionAwayToAway :
    ∃! f : Aₚ →+* Bₚ,
      f.comp (algebraMap A Aₚ) = (algebraMap B₀ Bₚ).comp j₀ ∧
        (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀) f := by
  apply D.existsUnique_localization_lift (Submonoid.powers (p : A)) Aₚ
    D.powers_p_frobenius_stable (deltaPDivisionAwayStructure E₀)
    ((algebraMap B₀ Bₚ).comp j₀)
    ((deltaPDivisionAwayStructure_base_isDeltaHom E₀).comp
      (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a))
  apply map_powers_isUnit
  have hp := IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B₀)
  have he : ((algebraMap B₀ Bₚ).comp j₀) (p : A) = algebraMap B₀ Bₚ (p : B₀) :=
    congrArg (algebraMap B₀ Bₚ) (map_natCast j₀ p)
  exact he.symm ▸ hp

/-- 局所化間の正方向の具体的δ射。 -/
def deltaPDivisionAwayToAway : Aₚ →+* Bₚ :=
  (existsUnique_deltaPDivisionAwayToAway D a).choose

/-- 正方向の局所化射は標準基底射とδ構造を保つ。 -/
theorem deltaPDivisionAwayToAway_spec :
    (deltaPDivisionAwayToAway D a).comp (algebraMap A Aₚ) = (algebraMap B₀ Bₚ).comp j₀ ∧
      (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀)
        (deltaPDivisionAwayToAway D a) :=
  (existsUnique_deltaPDivisionAwayToAway D a).choose_spec.1

/-- rawδ射はp除算添加環のp局所化から一意に延長する。 -/
theorem existsUnique_deltaPDivisionAwayFromAway :
    ∃! f : Bₚ →+* Aₚ,
      f.comp (algebraMap B₀ Bₚ) = deltaPDivisionToAway D a ∧
        (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D) f := by
  apply (E₀).existsUnique_localization_lift (Submonoid.powers (p : B₀)) Bₚ
    (E₀).powers_p_frobenius_stable (deltaPDivisionAwayStructure D)
    (deltaPDivisionToAway D a) (deltaPDivisionToAway_spec D a).1
  apply map_powers_isUnit
  have hp := IsLocalization.Away.algebraMap_isUnit (S := Aₚ) (p : A)
  have he : deltaPDivisionToAway D a (p : B₀) = algebraMap A Aₚ (p : A) :=
    (map_natCast (deltaPDivisionToAway D a) p).trans (map_natCast (algebraMap A Aₚ) p).symm
  exact he.symm ▸ hp

/-- 局所化間の逆方向の具体的δ射。 -/
def deltaPDivisionAwayFromAway : Bₚ →+* Aₚ :=
  (existsUnique_deltaPDivisionAwayFromAway D a).choose

/-- 逆方向の局所化射も標準単位とδ構造を保つ。 -/
theorem deltaPDivisionAwayFromAway_spec :
    (deltaPDivisionAwayFromAway D a).comp (algebraMap B₀ Bₚ) = deltaPDivisionToAway D a ∧
      (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D)
        (deltaPDivisionAwayFromAway D a) :=
  (existsUnique_deltaPDivisionAwayFromAway D a).choose_spec.1

/-- rawδ包上では、正方向と具体的δ評価の合成は標準p局所化射。 -/
theorem deltaPDivisionAwayToAway_comp_toAway :
    (deltaPDivisionAwayToAway D a).comp (deltaPDivisionToAway D a) = algebraMap B₀ Bₚ := by
  let g := (algebraMap B₀ Bₚ).comp j₀
  have hg : D.IsDeltaHom (deltaPDivisionAwayStructure E₀) g :=
    (deltaPDivisionAwayStructure_base_isDeltaHom E₀).comp
      (deltaAdjoinDivisionMap_isDeltaHom D (p : A) a)
  have hp : IsUnit (g (p : A)) := by
    have he : g (p : A) = algebraMap B₀ Bₚ (p : B₀) :=
      congrArg (algebraMap B₀ Bₚ) (map_natCast j₀ p)
    exact he.symm ▸ IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B₀)
  obtain ⟨u, hu⟩ := hp
  have ha : ∀ s, g (p : A) ∣ g (a s) := by
    intro s
    refine ⟨(u⁻¹ : Bₚˣ) * g (a s), ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  obtain ⟨f, _, hf⟩ := existsUnique_deltaAdjoinDivisionHom_of_regular D
    (deltaPDivisionAwayStructure E₀) (p : A) a g hg
    (fun _ _ h ↦ (show IsUnit (g (p : A)) from hu ▸ u.isUnit).mul_left_cancel h) ha
  have h₁ : ((deltaPDivisionAwayToAway D a).comp (deltaPDivisionToAway D a)).comp j₀ = g := by
    rw [RingHom.comp_assoc, (deltaPDivisionToAway_spec D a).2.1,
      (deltaPDivisionAwayToAway_spec D a).1]
  exact (hf _ ⟨(deltaPDivisionAwayToAway_spec D a).2.comp (deltaPDivisionToAway_spec D a).1,
    h₁⟩).trans (hf _ ⟨deltaPDivisionAwayStructure_base_isDeltaHom E₀, rfl⟩).symm

/-- 正逆方向の局所化射の合成はA[1/p]の恒等射。 -/
theorem deltaPDivisionAwayFromAway_comp_toAway :
    (deltaPDivisionAwayFromAway D a).comp (deltaPDivisionAwayToAway D a) = RingHom.id Aₚ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
  rw [RingHom.comp_assoc, (deltaPDivisionAwayToAway_spec D a).1, ← RingHom.comp_assoc,
    (deltaPDivisionAwayFromAway_spec D a).1, (deltaPDivisionToAway_spec D a).2.1,
    RingHom.id_comp]

/-- 逆順の局所化射の合成も恒等射。 -/
theorem deltaPDivisionAwayToAway_comp_fromAway :
    (deltaPDivisionAwayToAway D a).comp (deltaPDivisionAwayFromAway D a) = RingHom.id Bₚ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : B₀))
  rw [RingHom.comp_assoc, (deltaPDivisionAwayFromAway_spec D a).1,
    deltaPDivisionAwayToAway_comp_toAway, RingHom.id_comp]

/-- 一般元族のraw p除算添加環のp局所化はA[1/p]と具体的に同型。 -/
def deltaPDivisionLocalizationEquiv : Aₚ ≃+* Bₚ :=
  RingEquiv.ofRingHom (deltaPDivisionAwayToAway D a) (deltaPDivisionAwayFromAway D a)
    (deltaPDivisionAwayToAway_comp_fromAway D a) (deltaPDivisionAwayFromAway_comp_toAway D a)

/-- 局所化比較同型の両方向はδ構造と両立する。 -/
theorem deltaPDivisionLocalizationEquiv_isDeltaHom :
    (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E₀)
        (deltaPDivisionLocalizationEquiv D a).toRingHom ∧
      (deltaPDivisionAwayStructure E₀).IsDeltaHom (deltaPDivisionAwayStructure D)
        (deltaPDivisionLocalizationEquiv D a).symm.toRingHom :=
  ⟨(deltaPDivisionAwayToAway_spec D a).2, (deltaPDivisionAwayFromAway_spec D a).2⟩

/-- 局所化比較同型は元のAからの標準射を保つ。 -/
theorem deltaPDivisionLocalizationEquiv_comp_base :
    (deltaPDivisionLocalizationEquiv D a).toRingHom.comp (algebraMap A Aₚ) =
      (algebraMap B₀ Bₚ).comp j₀ := (deltaPDivisionAwayToAway_spec D a).1

/-- 逆比較同型はrawδ包からの標準射を具体的δ評価へ送る。 -/
theorem deltaPDivisionLocalizationEquiv_symm_comp_base :
    (deltaPDivisionLocalizationEquiv D a).symm.toRingHom.comp (algebraMap B₀ Bₚ) =
      deltaPDivisionToAway D a := (deltaPDivisionAwayFromAway_spec D a).1

end SerrePositivity.BhattScholze

end DeltaPDivisionLocalization

/-! ## raw φ(y)/p包の具体的な階乗分母

任意の元族を許し、正則性を要求しない。選んだ元の階乗を払った式を示す。
これだけでは分冪構造の公理・分冪包の普遍性を結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionFactorial

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (y : σ → A)
local notation "a₀" => fun s ↦ D.frobeniusLift (y s)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "E₀" => deltaAdjoinDivisionStructure D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "v₀" => deltaAdjoinDivisionVariable D (p : A) a₀

/-- rawφ除算包で、j(y_s)^p/pはv_s−j(δ(y_s))として存在する。 -/
theorem deltaPDivisionRaw_prime_dvd_pow (s : σ) : (p : B₀) ∣ j₀ (y s) ^ p := by
  have hp : j₀ (p : A) = (p : B₀) := map_natCast j₀ p
  have h := deltaAdjoinDivision_relation D (p : A) a₀ s
  rw [hp] at h
  refine ⟨v₀ s - j₀ (D.delta (y s)), ?_⟩
  calc
    j₀ (y s) ^ p = j₀ (D.frobeniusLift (y s)) - (p : B₀) * j₀ (D.delta (y s)) := by
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, hp]
      ring
    _ = (p : B₀) * (v₀ s - j₀ (D.delta (y s))) := by
      change j₀ (a₀ s) - _ = _
      rw [← h, mul_sub]

/-- 非p倍の自然数がAの単元なら、raw包のj(y_s)は全階乗で除算できる。 -/
theorem deltaPDivisionRaw_factorial_dvd_pow
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    (n.factorial : B₀) ∣ j₀ (y s) ^ n := by
  apply (E₀).factorial_dvd_pow_of_prime_dvd_pow
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map j₀)
    (deltaPDivisionRaw_prime_dvd_pow D y s)

/-- raw包内に選んだj(y_s)^n/n!。正則性なしでは分母を払う式で指定する。 -/
def deltaPDivisionRawFactorialQuotient
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) : B₀ :=
  (deltaPDivisionRaw_factorial_dvd_pow D y hlocal s n).choose

/-- 選んだ元はn!を掛けるとj(y_s)^nに戻る。 -/
theorem deltaPDivisionRawFactorialQuotient_spec
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    (n.factorial : B₀) * deltaPDivisionRawFactorialQuotient D y hlocal s n =
      j₀ (y s) ^ n :=
  (deltaPDivisionRaw_factorial_dvd_pow D y hlocal s n).choose_spec.symm

/-- 0番目の階乗分母は1。 -/
theorem deltaPDivisionRawFactorialQuotient_zero
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    deltaPDivisionRawFactorialQuotient D y hlocal s 0 = 1 := by
  simpa using deltaPDivisionRawFactorialQuotient_spec D y hlocal s 0

/-- 1番目の階乗分母は元の基底元。 -/
theorem deltaPDivisionRawFactorialQuotient_one
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    deltaPDivisionRawFactorialQuotient D y hlocal s 1 = j₀ (y s) := by
  simpa using deltaPDivisionRawFactorialQuotient_spec D y hlocal s 1

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorial

/-! ## rawδ除算包の像のδ安定部分環としての最小性

相対自由δ環の反復δ座標と商の帰納法による。p正則性は不要。
分冪包候補への適用には、その候補のδ安定性を別途証明する必要がある。
-/

@[expose] public noncomputable section DeltaPDivisionRawMinimal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 基底と初期変数の像を含むδ安定部分環は、raw包のδ射の全像を含む。 -/
theorem deltaAdjoinDivision_range_le_of_delta_stable {T : Type w} [CommRing T]
    (D : DeltaStructure p A) (E : DeltaStructure p T) (d : A) (a : σ → A)
    (f : DeltaAdjoinDivision D d a →+* T)
    (hf : (deltaAdjoinDivisionStructure D d a).IsDeltaHom E f) (S : Subring T)
    (hbase : ∀ r : A, f (deltaAdjoinDivisionMap D d a r) ∈ S)
    (hvar : ∀ s : σ, f (deltaAdjoinDivisionVariable D d a s) ∈ S)
    (hδ : ∀ t ∈ S, E.delta t ∈ S) : f.range ≤ S := by
  let F := relativeFreeDeltaStructure σ D
  let I := F.deltaClosure (deltaDivisionRelationIdeal d a)
  let q := Ideal.Quotient.mk I
  let g := f.comp q
  have hg : F.IsDeltaHom E g := hf.comp (F.isDeltaHom_quotient_mk I (F.isStable_deltaClosure _))
  have hX (s : σ) (n : ℕ) : g (MvPolynomial.X (s, n)) ∈ S := by
    rw [relativeFreeDeltaHom_X_iterates D E g hg s n]
    change E.delta^[n] (f (deltaAdjoinDivisionVariable D d a s)) ∈ S
    induction n with
    | zero => exact hvar s
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hδ _ ih
  rintro t ⟨b, rfl⟩
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective b
  change g P ∈ S
  induction P using MvPolynomial.induction_on with
  | C r => exact hbase r
  | add P Q hP hQ => rw [map_add]; exact S.add_mem hP hQ
  | mul_X P z hP => rw [map_mul]; exact S.mul_mem hP (hX z.1 z.2)

/-- Aとy_s^p/pを含むδ安定部分環は、具体的A{φ(y_s)/p}の局所化内の像を含む。 -/
theorem deltaPDivisionToAway_range_le_of_delta_stable (D : DeltaStructure p A)
    (y : σ → A) (S : Subring (Localization.Away (p : A)))
    (hbase : ∀ r : A, algebraMap A (Localization.Away (p : A)) r ∈ S)
    (hpow : ∀ s : σ, IsLocalization.Away.invSelf (p : A) *
      (algebraMap A (Localization.Away (p : A)) (y s)) ^ p ∈ S)
    (hδ : ∀ t ∈ S, (deltaPDivisionAwayStructure D).delta t ∈ S) :
    (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range ≤ S := by
  let a := fun s ↦ D.frobeniusLift (y s)
  let f := deltaPDivisionToAway D a
  apply deltaAdjoinDivision_range_le_of_delta_stable D (deltaPDivisionAwayStructure D)
    (p : A) a f (deltaPDivisionToAway_spec D a).1 S ?_ ?_ hδ
  · intro r
    have hb := RingHom.congr_fun (deltaPDivisionToAway_spec D a).2.1 r
    exact hb ▸ hbase r
  · intro s
    have he : f (deltaAdjoinDivisionVariable D (p : A) a s) =
        IsLocalization.Away.invSelf (p : A) *
          (algebraMap A (Localization.Away (p : A)) (y s)) ^ p +
          algebraMap A (Localization.Away (p : A)) (D.delta (y s)) := by
      rw [(deltaPDivisionToAway_spec D a).2.2]
      change _ * algebraMap A _ (D.frobeniusLift (y s)) = _
      have hi : IsLocalization.Away.invSelf (p : A) *
          algebraMap A (Localization.Away (p : A)) (p : A) = 1 := by
        rw [mul_comm, IsLocalization.Away.mul_invSelf]
      rw [D.frobeniusLift_apply, map_add, map_pow, map_mul, mul_add,
        ← mul_assoc, hi, one_mul]
    rw [he]
    exact S.add_mem (hpow s) (hbase _)

end SerrePositivity.BhattScholze

end DeltaPDivisionRawMinimal

/-! ## A[1/p]内の階乗分母生成部分環とrawδ評価の像

実際の部分環とその生成元を比較する。逆包含にはδ安定性を明示する。
この入力の解消、分冪包の普遍性、CFFは別工程。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialSubring

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- raw包で選んだ階乗分母の実局所化像は、局所化内の正規化された階乗分母。 -/
theorem deltaPDivisionToAway_factorialQuotient (D : DeltaStructure p A) (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) (n : ℕ) :
    deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))
      (deltaPDivisionRawFactorialQuotient D y hlocal s n) =
        pDivisionFactorialValue p y s n := by
  let f := deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))
  have h := congrArg f (deltaPDivisionRawFactorialQuotient_spec D y hlocal s n)
  simp only [map_mul, map_natCast, map_pow] at h
  have hb := RingHom.congr_fun (deltaPDivisionToAway_spec D
    (fun s ↦ D.frobeniusLift (y s))).2.1 (y s)
  change f (deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) (y s)) = _ at hb
  rw [hb] at h
  change f _ = Ring.inverse _ * _
  rw [← h, Ring.inverse_mul_cancel_left _ _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial (Nat.factorial_ne_zero n))]

/-- 具体的な全階乗分母の生成部分環はrawδ評価の実像に含まれる。 -/
theorem pDivisionFactorialSubring_le_raw_range (D : DeltaStructure p A) (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) :
    pDivisionFactorialSubring p y ≤
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range := by
  apply Subring.closure_le.mpr
  rintro t (⟨r, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
  · exact ⟨deltaAdjoinDivisionMap D (p : A) (fun s ↦ D.frobeniusLift (y s)) r,
      RingHom.congr_fun (deltaPDivisionToAway_spec D (fun s ↦ D.frobeniusLift (y s))).2.1 r⟩
  · exact ⟨deltaPDivisionRawFactorialQuotient D y hlocal s n,
      deltaPDivisionToAway_factorialQuotient D y hlocal s n⟩

/-- y_s^p/pは(p−1)!倍のp番目の階乗分母として生成部分環に入る。 -/
theorem pDivisionFactorialSubring_pow_div_prime_mem (y : σ → A)
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (s : σ) :
    IsLocalization.Away.invSelf (p : A) *
      (algebraMap A (Localization.Away (p : A)) (y s)) ^ p ∈ pDivisionFactorialSubring p y := by
  let L := Localization.Away (p : A)
  have hp : IsUnit (p : L) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := L) (p : A)
  have hinv : (p : L) * Ring.inverse (p.factorial : L) * ((p - 1).factorial : L) = 1 := by
    calc
      _ = (p.factorial : L) * Ring.inverse (p.factorial : L) := by
        rw [← Nat.mul_factorial_pred (Fact.out : p.Prime).ne_zero, Nat.cast_mul]
        ring
      _ = 1 := Ring.mul_inverse_cancel _
        (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal p.factorial
          (Nat.factorial_ne_zero p))
  have he : IsLocalization.Away.invSelf (p : A) * (algebraMap A L (y s)) ^ p =
      ((p - 1).factorial : L) * pDivisionFactorialValue p y s p := by
    apply hp.mul_left_cancel
    change (p : L) * (_ * _) = (p : L) * (_ * (Ring.inverse _ * _))
    rw [← mul_assoc, ← map_natCast (algebraMap A L), IsLocalization.Away.mul_invSelf, one_mul]
    calc
      _ = (1 : L) * (algebraMap A L (y s)) ^ p := (one_mul _).symm
      _ = _ := by rw [← hinv, map_natCast]; ring
  rw [he]
  apply (pDivisionFactorialSubring p y).mul_mem
  · simpa only [map_natCast] using
      pDivisionFactorialSubring_coeff_mem (p := p) y ((p - 1).factorial : A)
  · exact pDivisionFactorialSubring_value_mem y s p

/-- 生成部分環のδ安定性を供給すれば、rawδ評価の像との一致が従う。 -/
theorem pDivisionFactorialSubring_eq_raw_range_of_delta_stable (D : DeltaStructure p A)
    (y : σ → A) (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hδ : ∀ t ∈ pDivisionFactorialSubring p y,
      (deltaPDivisionAwayStructure D).delta t ∈ pDivisionFactorialSubring p y) :
    pDivisionFactorialSubring p y =
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range := by
  apply le_antisymm (pDivisionFactorialSubring_le_raw_range D y hlocal)
  exact deltaPDivisionToAway_range_le_of_delta_stable D y _
    (pDivisionFactorialSubring_coeff_mem y)
    (pDivisionFactorialSubring_pow_div_prime_mem y hlocal) hδ

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialSubring

/-! ## 実局所化δ構造での階乗生成元の展開

環同型に沿った別のδ作用ではなく、既存の局所化δ作用を直接計算する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialDelta

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
local notation "L₀" => Localization.Away (p : A)

/-- 局所化内のRing.inverseによる分母は、既存ℚ作用による1/n!に等しい。 -/
theorem pDivisionFactorialValue_eq_rat (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    pDivisionFactorialValue p y s n =
      algebraMap ℚ L₀ (1 / (n.factorial : ℚ)) * (algebraMap A L₀ (y s)) ^ n := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  have hu : IsUnit (n.factorial : ℚ) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have he := hu.map_ringInverse (algebraMap ℚ L₀)
  rw [Ring.inverse_eq_inv, map_natCast] at he
  change Ring.inverse _ * _ = _
  rw [one_div, he]

/-- 実局所化のFrobeniusは階乗生成元に通常のφ(y)=y^p+pδ(y)を適用する。 -/
theorem pDivisionFactorialValue_frobeniusLift (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    (deltaPDivisionAwayStructure D).frobeniusLift (pDivisionFactorialValue p y s n) =
      algebraMap ℚ L₀ (1 / (n.factorial : ℚ)) *
        ((algebraMap A L₀ (y s)) ^ p + (p : L₀) * algebraMap A L₀ (D.delta (y s))) ^ n := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  rw [pDivisionFactorialValue_eq_rat hlocal, map_mul, map_pow, RingHom.map_rat_algebraMap]
  rw [DeltaStructure.frobeniusLift_apply,
    ← deltaPDivisionAwayStructure_base_isDeltaHom D (y s)]

/-- 実局所化でのδ(γ_n(y_s))を、p可積分係数と階乗分母の有限和で書く。 -/
theorem pDivisionFactorialValue_delta_expansion (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    letI := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    (deltaPDivisionAwayStructure D).delta (pDivisionFactorialValue p y s n) =
      (∑ i ∈ Finset.range (n + 1),
        algebraMap ℚ L₀ (dividedPowerFrobeniusCoefficient p n i) *
          pDivisionFactorialValue p y s (p * i) * (algebraMap A L₀ (D.delta (y s))) ^ (n - i)) -
      algebraMap ℚ L₀ (dividedPowerPowerCoefficient p n) *
        pDivisionFactorialValue p y s (p * n) := by
  let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  let f := algebraMap ℚ L₀
  let E := deltaPDivisionAwayStructure D
  let c := pDivisionFactorialValue p y s n
  let x := algebraMap A L₀ (y s)
  let z := algebraMap A L₀ (D.delta (y s))
  have hpinv : f (1 / (p : ℚ)) * (p : L₀) = 1 := by
    have he : (1 / (p : ℚ)) * (p : ℚ) = 1 := by
      exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    simpa only [map_mul, map_natCast, map_one] using congrArg f he
  have hd : E.delta c = f (1 / (p : ℚ)) * (E.frobeniusLift c - c ^ p) := by
    rw [E.frobeniusLift_apply, add_sub_cancel_left, ← mul_assoc, hpinv, one_mul]
  have hs : f (1 / (p : ℚ)) * f (1 / (n.factorial : ℚ)) =
      f (1 / ((p : ℚ) * (n.factorial : ℚ))) := by
    rw [← map_mul, one_div_mul_one_div]
  have hF : f (1 / (p : ℚ)) * E.frobeniusLift c =
      ∑ i ∈ Finset.range (n + 1), f (dividedPowerFrobeniusCoefficient p n i) *
        pDivisionFactorialValue p y s (p * i) * z ^ (n - i) := by
    rw [pDivisionFactorialValue_frobeniusLift hlocal D, ← mul_assoc, hs]
    simpa only [map_natCast, pDivisionFactorialValue_eq_rat hlocal] using
      (dividedPower_frobenius_expansion (p := p) f x z n)
  have hP : f (1 / (p : ℚ)) * c ^ p =
      f (dividedPowerPowerCoefficient p n) * pDivisionFactorialValue p y s (p * n) := by
    dsimp only [c]
    simpa only [pDivisionFactorialValue_eq_rat hlocal] using
      (dividedPower_power_expansion (p := p) f x n)
  rw [hd, mul_sub, hF, hP]


include hlocal in
/-- 各階乗生成元の実δ像は、具体的な階乗生成部分環に入る。 -/
theorem pDivisionFactorialValue_delta_mem (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    (deltaPDivisionAwayStructure D).delta (pDivisionFactorialValue p y s n) ∈
      pDivisionFactorialSubring p y := by
  by_cases hn : n = 0
  · subst n
    have he : pDivisionFactorialValue p y s 0 = 1 := by simp [pDivisionFactorialValue]
    rw [he, DeltaStructure.delta_one]
    exact (pDivisionFactorialSubring p y).zero_mem
  · let := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
    rw [pDivisionFactorialValue_delta_expansion hlocal D]
    apply (pDivisionFactorialSubring p y).sub_mem
    · apply (pDivisionFactorialSubring p y).sum_mem
      intro i hi
      apply (pDivisionFactorialSubring p y).mul_mem
      · apply (pDivisionFactorialSubring p y).mul_mem
        · obtain ⟨a, ha⟩ := dividedPowerFrobeniusCoefficient_mem_baseRange hlocal n i hn
            (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
          rw [← ha]
          exact pDivisionFactorialSubring_coeff_mem y a
        · exact pDivisionFactorialSubring_value_mem y s (p * i)
      · exact (pDivisionFactorialSubring p y).pow_mem
          (pDivisionFactorialSubring_coeff_mem y (D.delta (y s))) _
    · apply (pDivisionFactorialSubring p y).mul_mem
      · obtain ⟨a, ha⟩ := dividedPowerPowerCoefficient_mem_baseRange hlocal n hn
        rw [← ha]
        exact pDivisionFactorialSubring_coeff_mem y a
      · exact pDivisionFactorialSubring_value_mem y s (p * n)

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialDelta

/-! ## 階乗生成部分環の実δ安定性とraw像の同定

Witt繰上り項の部分環内閉性を含めて生成帰納法を検証する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialStable

namespace SerrePositivity.BhattScholze
namespace DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 同じ部分環内の2元のWitt加法繰上り項は、同じ部分環内にある。 -/
theorem additionCarry_mem_subring (S : Subring A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) :
    (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 ∈ S := by
  let xS : S := ⟨x, hx⟩
  let yS : S := ⟨y, hy⟩
  let c : S := (WittVector.teichmuller p xS + WittVector.teichmuller p yS).coeff 1
  have he : (WittVector.teichmuller p x + WittVector.teichmuller p y).coeff 1 = S.subtype c := by
    dsimp only [c]
    rw [← WittVector.map_coeff, map_add, WittVector.map_teichmuller, WittVector.map_teichmuller]
    rfl
  rw [he]
  exact c.property

/-- 生成元のδが生成部分環内にあれば、生成部分環全体のδが内部にある。 -/
theorem delta_mem_subringClosure (D : DeltaStructure p A) (s : Set A)
    (hs : ∀ x ∈ s, D.delta x ∈ Subring.closure s) (x : A) (hx : x ∈ Subring.closure s) :
    D.delta x ∈ Subring.closure s := by
  let S := Subring.closure s
  induction hx using Subring.closure_induction with
  | mem x hx => exact hs x hx
  | zero => rw [D.delta_zero]; exact S.zero_mem
  | one => rw [D.delta_one]; exact S.zero_mem
  | add x y hx hy hdx hdy =>
      rw [D.delta_add]
      exact S.add_mem (S.add_mem hdx hdy) (additionCarry_mem_subring S hx hy)
  | neg x hx hdx =>
      have hc := additionCarry_mem_subring (p := p) S hx (S.neg_mem hx)
      have h := D.delta_add x (-x)
      rw [add_neg_cancel, D.delta_zero] at h
      have he : D.delta (-x) =
          -(D.delta x + (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1) := by
        calc
          _ = (D.delta x + D.delta (-x) +
              (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1) -
              D.delta x -
              (WittVector.teichmuller p x + WittVector.teichmuller p (-x)).coeff 1 := by ring
          _ = _ := by rw [← h]; ring
      rw [he]
      exact S.neg_mem (S.add_mem hdx hc)
  | mul x y hx hy hdx hdy =>
      rw [D.delta_mul]
      exact S.add_mem (S.add_mem (S.mul_mem (S.pow_mem hx p) hdy)
        (S.mul_mem hdx (S.pow_mem hy p)))
        (S.mul_mem (S.mul_mem (natCast_mem S p) hdx) hdy)

end DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- p局所性の下で、具体的な階乗生成部分環は既存の局所化δ構造で安定。 -/
theorem pDivisionFactorialSubring_delta_mem (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) (t : Localization.Away (p : A))
    (ht : t ∈ pDivisionFactorialSubring p y) :
    (deltaPDivisionAwayStructure D).delta t ∈ pDivisionFactorialSubring p y := by
  apply (deltaPDivisionAwayStructure D).delta_mem_subringClosure _ ?_ t ht
  rintro x (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
  · rw [← deltaPDivisionAwayStructure_base_isDeltaHom D a]
    exact pDivisionFactorialSubring_coeff_mem y (D.delta a)
  · exact pDivisionFactorialValue_delta_mem hlocal D y s n

/-- p局所性だけで、階乗生成部分環はrawφ除算包の実局所化像に一致する（BS 著者版 Lemma 2.36 の p 局所 δ 環の A[1/p] 内の像の記述）。 -/
theorem pDivisionFactorialSubring_eq_raw_range (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) :
    pDivisionFactorialSubring p y =
      (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range :=
  pDivisionFactorialSubring_eq_raw_range_of_delta_stable D y hlocal
    (pDivisionFactorialSubring_delta_mem hlocal D y)


/-- φによる捻りを含むraw包の局所化内の像は、基底のδ構造の選び方に依存しない。 -/
theorem deltaPDivisionToAway_range_eq_of_deltaStructure
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D E : DeltaStructure p A) (y : σ → A) :
    (deltaPDivisionToAway D (fun s ↦ D.frobeniusLift (y s))).range =
      (deltaPDivisionToAway E (fun s ↦ E.frobeniusLift (y s))).range :=
  (pDivisionFactorialSubring_eq_raw_range hlocal D y).symm.trans
    (pDivisionFactorialSubring_eq_raw_range hlocal E y)

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialStable

/-! ## 具体的階乗生成部分環のδ構造と分冪作用

元のAにはp正則性を課さず、局所化内の部分環のp正則性を直接使う。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialStructure

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
local notation "L₀" => Localization.Away (p : A)
local notation "S₀" => pDivisionFactorialSubring p

/-- 元のAから具体的階乗生成部分環への実標準射。 -/
def pDivisionFactorialBase (p : ℕ) (y : σ → A) : A →+* pDivisionFactorialSubring p y :=
  (algebraMap A (Localization.Away (p : A))).codRestrict _ (pDivisionFactorialSubring_coeff_mem y)

/-- δ安定性により制限した、具体的階乗生成部分環のδ構造。 -/
def pDivisionFactorialDelta (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (D : DeltaStructure p A) (y : σ → A) : DeltaStructure p (S₀ y) :=
  (deltaPDivisionAwayStructure D).subring (S₀ y) (pDivisionFactorialSubring_delta_mem hlocal D y)

/-- 具体的階乗生成部分環の局所化への包含はδ射。 -/
theorem pDivisionFactorialDelta_subtype_isDeltaHom
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    (pDivisionFactorialDelta hlocal D y).IsDeltaHom (deltaPDivisionAwayStructure D)
      (S₀ y).subtype :=
  (deltaPDivisionAwayStructure D).subring_subtype_isDeltaHom _ _

/-- 元のAからの実基底射もδ射。 -/
theorem pDivisionFactorialDelta_base_isDeltaHom
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    D.IsDeltaHom (pDivisionFactorialDelta hlocal D y) (pDivisionFactorialBase p y) := by
  intro a
  apply Subtype.ext
  exact deltaPDivisionAwayStructure_base_isDeltaHom D a

omit [Fact p.Prime] in
/-- pは局所化内で単元なので、階乗生成部分環内ではp正則。 -/
theorem pDivisionFactorial_p_mul_injective (y : σ → A) :
    Function.Injective (fun x : S₀ y ↦ (p : S₀ y) * x) := by
  have hp : IsUnit (p : L₀) := by
    simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := L₀) (p : A)
  intro x z hxz
  apply Subtype.ext
  apply hp.mul_left_cancel
  exact congrArg (fun t : S₀ y ↦ (t : L₀)) hxz

/-- 具体的部分環のp除算可能イデアル上の既存の標準分冪構造。 -/
def pDivisionFactorialDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    DividedPowers (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal :=
  (pDivisionFactorialDelta hlocal D y).primeDividedPowers (pDivisionFactorial_p_mul_injective y)
    (fun m hm ↦ by simpa only [map_natCast] using (hlocal m hm).map (pDivisionFactorialBase p y))

/-- 各基底元y_sは、この部分環のp除算可能イデアルに入る。 -/
theorem pDivisionFactorialBase_mem_primeIdeal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) :
    pDivisionFactorialBase p y (y s) ∈
      (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal := by
  apply ((pDivisionFactorialDelta hlocal D y).mem_primeDividedPowerIdeal _).mpr
  refine ⟨⟨IsLocalization.Away.invSelf (p : A) * (algebraMap A L₀ (y s)) ^ p,
    pDivisionFactorialSubring_pow_div_prime_mem y hlocal s⟩, ?_⟩
  apply Subtype.ext
  change (algebraMap A L₀ (y s)) ^ p = (p : L₀) *
    (IsLocalization.Away.invSelf (p : A) * (algebraMap A L₀ (y s)) ^ p)
  rw [← mul_assoc, ← map_natCast (algebraMap A L₀), IsLocalization.Away.mul_invSelf, one_mul]

/-- 実分冪作用の値は、局所化内の正規化された階乗分母と一致する。 -/
theorem pDivisionFactorialDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    ((pDivisionFactorialDividedPowers hlocal D y).dpow n
      (pDivisionFactorialBase p y (y s)) : L₀) = pDivisionFactorialValue p y s n := by
  have hu := DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)
  apply hu.mul_left_cancel
  change (n.factorial : L₀) * _ = (n.factorial : L₀) * (Ring.inverse _ * _)
  rw [Ring.mul_inverse_cancel_left _ _ hu]
  have h := (pDivisionFactorialDividedPowers hlocal D y).factorial_mul_dpow_eq_pow
    (pDivisionFactorialBase_mem_primeIdeal hlocal D y s) (n := n)
  exact congrArg (fun t : S₀ y ↦ (t : L₀)) h

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialStructure

/-! ## 正次数の階乗分母の生成イデアルの実分冪構造

既存SubDPIdeal.spanの生成表示を具体的な階乗生成元へ同定する。
分冪包の普遍性は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialIdeal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
local notation "S₀" => pDivisionFactorialSubring p
local notation "L₀" => Localization.Away (p : A)

/-- 正次数の階乗分母γ_(n+1)(y_s)が生成する、具体的部分環内のイデアル。 -/
def pDivisionFactorialIdeal (p : ℕ) (y : σ → A) : Ideal (pDivisionFactorialSubring p y) :=
  Ideal.span (Set.range (fun z : σ × ℕ ↦
    (⟨pDivisionFactorialValue p y z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem y z.1 (z.2 + 1)⟩ : pDivisionFactorialSubring p y)))

omit [Fact p.Prime] in
/-- 各基底元y_sはγ_1(y_s)として、この具体的なイデアルに入る。 -/
theorem pDivisionFactorialBase_mem_factorialIdeal (y : σ → A) (s : σ) :
    pDivisionFactorialBase p y (y s) ∈ pDivisionFactorialIdeal p y := by
  have h := Ideal.subset_span (s := Set.range (fun z : σ × ℕ ↦
    (⟨pDivisionFactorialValue p y z.1 (z.2 + 1),
      pDivisionFactorialSubring_value_mem y z.1 (z.2 + 1)⟩ : S₀ y))) (Set.mem_range_self (s, 0))
  have he : pDivisionFactorialBase p y (y s) =
      (⟨pDivisionFactorialValue p y s 1, pDivisionFactorialSubring_value_mem y s 1⟩ : S₀ y) := by
    apply Subtype.ext
    simp [pDivisionFactorialBase, pDivisionFactorialValue]
  rw [he]
  exact h

/-- 具体的イデアルは、基底元の既存の分冪生成イデアルそのもの。 -/
theorem pDivisionFactorialIdeal_eq_dpSpan
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    pDivisionFactorialIdeal p y =
      (DividedPowers.SubDPIdeal.span (pDivisionFactorialDividedPowers hlocal D y)
        (Set.range (fun s : σ ↦ pDivisionFactorialBase p y (y s)))).carrier := by
  have hS : Set.range (fun s : σ ↦ pDivisionFactorialBase p y (y s)) ⊆
      (pDivisionFactorialDelta hlocal D y).primeDividedPowerIdeal := by
    rintro _ ⟨s, rfl⟩
    exact pDivisionFactorialBase_mem_primeIdeal hlocal D y s
  rw [DividedPowers.SubDPIdeal.span_carrier_eq_dpow_span _ hS]
  apply congrArg Ideal.span
  ext t
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    refine ⟨n + 1, Nat.succ_ne_zero n, pDivisionFactorialBase p y (y s), ⟨s, rfl⟩, ?_⟩
    apply Subtype.ext
    exact (pDivisionFactorialDividedPowers_base_apply hlocal D y s (n + 1)).symm
  · rintro ⟨n, hn, _, ⟨s, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    refine ⟨(s, k), ?_⟩
    apply Subtype.ext
    exact (pDivisionFactorialDividedPowers_base_apply hlocal D y s (k + 1)).symm

/-- 具体的な正次数階乗イデアルは、最大p除算可能イデアルの分冪閉部分イデアル。 -/
theorem pDivisionFactorialIdeal_isSubDPIdeal
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    (pDivisionFactorialDividedPowers hlocal D y).IsSubDPIdeal (pDivisionFactorialIdeal p y) := by
  rw [pDivisionFactorialIdeal_eq_dpSpan hlocal D y]
  exact (DividedPowers.SubDPIdeal.span
    (pDivisionFactorialDividedPowers hlocal D y) _).toIsSubDPIdeal

/-- 具体的な正次数階乗イデアル上の、既存APIを制限した実分冪構造。 -/
def pDivisionFactorialIdealDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A) (y : σ → A) :
    DividedPowers (pDivisionFactorialIdeal p y) := by
  classical
  exact DividedPowers.IsSubDPIdeal.dividedPowers (pDivisionFactorialDividedPowers hlocal D y)
    (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)

/-- 正次数イデアル上の実分冪作用も、基底元で具体的な階乗分母に一致する。 -/
theorem pDivisionFactorialIdealDividedPowers_base_apply
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (D : DeltaStructure p A)
    (y : σ → A) (s : σ) (n : ℕ) :
    ((pDivisionFactorialIdealDividedPowers hlocal D y).dpow n
      (pDivisionFactorialBase p y (y s)) : L₀) = pDivisionFactorialValue p y s n := by
  classical
  rw [pDivisionFactorialIdealDividedPowers,
    DividedPowers.IsSubDPIdeal.dpow_eq_of_mem (pDivisionFactorialDividedPowers hlocal D y)
      (pDivisionFactorialIdeal_isSubDPIdeal hlocal D y)
      (pDivisionFactorialBase_mem_factorialIdeal (p := p) y s)]
  exact pDivisionFactorialDividedPowers_base_apply hlocal D y s n

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialIdeal

/-! ## q(y)=0となる通常係数射に沿うφ(y)/pの具体的Witt解

終域にδ構造を要求しない。全Witt係数の除算方程式を証明する。
rawδ反復関係を消す通常評価への移送・分冪包比較は別工程。
-/

@[expose] public noncomputable section DeltaPDivisionWittResidueSolution

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (q : A →+* B) (y : A)

/-- 基底Witt元の像の係数を一段ずらした、具体的なp除算解候補。 -/
def deltaPDivisionWittResidueSolution : WittVector p B :=
  WittVector.mk p (fun n ↦ q ((deltaWittGhostVector D y).coeff (n + 1)))

/-- 解候補の全Witt係数の具体式。 -/
theorem deltaPDivisionWittResidueSolution_coeff (n : ℕ) :
    (deltaPDivisionWittResidueSolution D q y).coeff n =
      q ((deltaWittGhostVector D y).coeff (n + 1)) := rfl

/-- q(y)=0なら、Verschiebungで元の基底Witt元の像へ戻る。 -/
theorem deltaPDivisionWittResidueSolution_verschiebung (hqy : q y = 0) :
    WittVector.verschiebung (deltaPDivisionWittResidueSolution D q y) =
      WittVector.map q (deltaWittGhostVector D y) := by
  ext n
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, WittVector.map_coeff,
      deltaWittGhostVector_coeff_zero, hqy]
  | succ n => rw [WittVector.verschiebung_coeff_succ,
      deltaPDivisionWittResidueSolution_coeff, WittVector.map_coeff]

/-- 具体的候補はp*t=s(φ(y))という全Witt環内の方程式を満たす。 -/
theorem deltaPDivisionWittResidueSolution_mul
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) :
    (p : WittVector p B) * deltaPDivisionWittResidueSolution D q y =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) := by
  calc
    _ = WittVector.frobenius (WittVector.verschiebung
        (deltaPDivisionWittResidueSolution D q y)) := by
      rw [WittVector.frobenius_verschiebung, mul_comm]
    _ = WittVector.frobenius (WittVector.map q (deltaWittGhostVector D y)) := by
      rw [deltaPDivisionWittResidueSolution_verschiebung D q y hqy]
    _ = WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) :=
      ((WittVector.frobenius_isPoly p).map q (deltaWittGhostVector D y)).symm.trans
        (congrArg (WittVector.map q) (deltaWittGhostVector_frobenius D hg y))

/-- pを基底のWitt切断で表しても同じ具体的除算方程式。 -/
theorem deltaPDivisionWittResidueSolution_mul_source_prime
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) :
    WittVector.map q (deltaWittGhostVector D (p : A)) * deltaPDivisionWittResidueSolution D q y =
      WittVector.map q (deltaWittGhostVector D (D.frobeniusLift y)) := by
  have he : WittVector.map q (deltaWittGhostVector D (p : A)) = (p : WittVector p B) := by
    change WittVector.map q (deltaWittGhostRingHom D hg (p : A)) = _
    rw [map_natCast, map_natCast]
  rw [he]
  exact deltaPDivisionWittResidueSolution_mul D q y hg hqy

/-- 元の係数から来る全Witt関係を一度に消す係数ごとの式。 -/
theorem deltaPDivisionWittResidueSolution_coordinate_relation
    (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hqy : q y = 0) (n : ℕ) :
    (WittVector.map q (deltaWittGhostVector D (p : A)) *
      deltaPDivisionWittResidueSolution D q y).coeff n =
        q ((deltaWittGhostVector D (D.frobeniusLift y)).coeff n) := by
  have h := congrArg (fun w : WittVector p B ↦ w.coeff n)
    (deltaPDivisionWittResidueSolution_mul_source_prime D q y hg hqy)
  simpa only [WittVector.map_coeff] using h

/-- 源がp正則なら、解の第0係数は具体的にq(δy)。 -/
theorem deltaPDivisionWittResidueSolution_coeff_zero
    (hp : Function.Injective (fun x : A ↦ (p : A) * x)) :
    (deltaPDivisionWittResidueSolution D q y).coeff 0 = q (D.delta y) := by
  rw [deltaPDivisionWittResidueSolution_coeff, Nat.zero_add,
    deltaWittGhostVector_coeff_one D hp]

end SerrePositivity.BhattScholze

end DeltaPDivisionWittResidueSolution

/-! ## 具体的Witt解を用いるrawδ除算包からの通常環射

全Witt係数の消滅を既存jet比較で全δ関係の消滅へ移す。
終域のδ構造・p正則性・完備性は要求しない。
-/

@[expose] public noncomputable section DeltaPDivisionWittResidueEvaluation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B σ : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (q : A →+* B) (y : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "F₀" => relativeFreeDeltaStructure σ D
local notation "a₀" => fun s ↦ D.frobeniusLift (y s)

/-- 逆Witt座標に具体的な除算解の全係数を代入する通常環射。 -/
def deltaPDivisionWittResidueEval : L₀ →+* B :=
  (MvPolynomial.eval₂Hom q (fun z : σ × ℕ ↦
    (deltaPDivisionWittResidueSolution D q (y z.1)).coeff z.2)).comp
      (relativeFreeWittInverseMap D hpA).toRingHom

/-- 通常評価は元の係数射を保つ。 -/
theorem deltaPDivisionWittResidueEval_C (r : A) :
    deltaPDivisionWittResidueEval D hpA q y (MvPolynomial.C r) = q r := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (MvPolynomial.C r)) = _
  rw [show relativeFreeWittInverseMap D hpA (MvPolynomial.C r) = MvPolynomial.C r from
    AlgHom.commutes (relativeFreeWittInverseMap D hpA) r, MvPolynomial.eval₂Hom_C]

/-- 各自由変数のWitt係数は具体的除算解の対応する係数に写る。 -/
theorem deltaPDivisionWittResidueEval_coefficient (s : σ) (n : ℕ) :
    deltaPDivisionWittResidueEval D hpA q y (relativeFreeWittGhostCoefficient D s n) =
      (deltaPDivisionWittResidueSolution D q (y s)).coeff n := by
  change MvPolynomial.eval₂Hom q _
    (relativeFreeWittInverseMap D hpA (relativeFreeWittGhostCoefficient D s n)) = _
  rw [relativeFreeWittInverseMap_coefficient, MvPolynomial.eval₂Hom_X']

/-- 自由初期変数の全Witt元は具体的除算解そのものに写る。 -/
theorem deltaPDivisionWittResidueEval_witt_X (s : σ) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) =
        deltaPDivisionWittResidueSolution D q (y s) := by
  ext n
  rw [WittVector.map_coeff]
  exact deltaPDivisionWittResidueEval_coefficient D hpA q y s n

/-- 基底係数の全Witt元は元の通常係数射の像に写る。 -/
theorem deltaPDivisionWittResidueEval_witt_C
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀)) (r : A) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C r)) =
        WittVector.map q (deltaWittGhostVector D r) := by
  ext n
  rw [WittVector.map_coeff, deltaWittGhostVector_relativeFree_C_coeff D hgL,
    deltaPDivisionWittResidueEval_C, WittVector.map_coeff]

/-- 実初期除算関係のWitt元はこの通常評価によって零になる。 -/
theorem deltaPDivisionWittResidueEval_kills_witt_relation
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) :
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
        MvPolynomial.C (D.frobeniusLift (y s)))) = 0 := by
  change WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
    (deltaWittGhostRingHom F₀ hgL (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s)))) = 0
  rw [map_sub, map_mul, map_sub, map_mul]
  change WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (p : A))) *
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.X (s, 0))) -
    WittVector.map (deltaPDivisionWittResidueEval D hpA q y)
      (deltaWittGhostVector F₀ (MvPolynomial.C (D.frobeniusLift (y s)))) = 0
  rw [deltaPDivisionWittResidueEval_witt_C D hpA q y hgL,
    deltaPDivisionWittResidueEval_witt_X, deltaPDivisionWittResidueEval_witt_C D hpA q y hgL]
  exact sub_eq_zero.mpr (deltaPDivisionWittResidueSolution_mul_source_prime D q (y s) hgA (hqy s))

/-- 実除算関係のすべてのδ反復像が、この通常評価で零になる。 -/
theorem deltaPDivisionWittResidueEval_kills_iterated_relation
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) (n : ℕ) :
    deltaPDivisionWittResidueEval D hpA q y
      (deltaDivisionIteratedRelation D (p : A) a₀ s n) = 0 := by
  have hpL : Function.Injective (fun x : L₀ ↦ (p : L₀) * x) := by
    have h := (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
    have h' : IsSMulRegular L₀ (p : L₀) := by simpa only [map_natCast] using h
    intro x z hxz
    apply h'
    simpa only [smul_eq_mul] using hxz
  have hw := deltaPDivisionWittResidueEval_kills_witt_relation D hpA q y hgA hgL hqy s
  have hc : ∀ i ≤ n, deltaPDivisionWittResidueEval D hpA q y
      ((deltaWittGhostVector F₀ (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
        MvPolynomial.C (D.frobeniusLift (y s)))).coeff i) = 0 := by
    intro i _
    have h := congrArg (fun w : WittVector p B ↦ w.coeff i) hw
    simpa only [WittVector.map_coeff, WittVector.zero_coeff] using h
  have hj := (deltaWittGhostVector_jets_zero_iff F₀ hpL hgL
    (deltaPDivisionWittResidueEval D hpA q y)
    (MvPolynomial.C (p : A) * MvPolynomial.X (s, 0) -
      MvPolynomial.C (D.frobeniusLift (y s))) n).mpr hc
  exact hj n le_rfl

/-- 全δ関係を消す評価から得る、rawδ p除算包からの実通常環射。 -/
def deltaPDivisionWittResidueMap
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) : DeltaAdjoinDivision D (p : A) a₀ →+* B :=
  deltaDivisionIteratedRelationsLift D (p : A) a₀ (deltaPDivisionWittResidueEval D hpA q y)
    (deltaPDivisionWittResidueEval_kills_iterated_relation D hpA q y hgA hgL hqy)

/-- raw包からの実通常射は元の全自由環の評価を延長する。 -/
theorem deltaPDivisionWittResidueMap_comp_mk
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) :
    (deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy).comp
      (Ideal.Quotient.mk ((relativeFreeDeltaStructure σ D).deltaClosure
        (deltaDivisionRelationIdeal (p : A) a₀))) = deltaPDivisionWittResidueEval D hpA q y := rfl

/-- 実通常射は基底の係数射qを保つ。 -/
theorem deltaPDivisionWittResidueMap_coeff
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (r : A) :
    deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy
      (deltaAdjoinDivisionMap D (p : A) a₀ r) = q r :=
  deltaPDivisionWittResidueEval_C D hpA q y r

/-- 初期除算変数の像はq(δy_s)。 -/
theorem deltaPDivisionWittResidueMap_variable
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) (s : σ) :
    deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy
      (deltaAdjoinDivisionVariable D (p : A) a₀ s) = q (D.delta (y s)) := by
  have h := deltaPDivisionWittResidueEval_coefficient D hpA q y s 0
  exact h.trans (deltaPDivisionWittResidueSolution_coeff_zero D q (y s) hpA)

/-- 元のAからの標準射と実通常射の合成はqそのもの。 -/
theorem deltaPDivisionWittResidueMap_comp_base
    (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
    (hgL : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (hqy : ∀ s, q (y s) = 0) :
    (deltaPDivisionWittResidueMap D hpA q y hgA hgL hqy).comp
      (deltaAdjoinDivisionMap D (p : A) a₀) = q := by
  ext r
  exact deltaPDivisionWittResidueMap_coeff D hpA q y hgA hgL hqy r

end SerrePositivity.BhattScholze

end DeltaPDivisionWittResidueEvaluation

/-! ## 具体的階乗部分環と正次数イデアルの関手的な写像

Mathlibの局所化写像を用い、基底と階乗生成元上の式を保つ実環射を構成する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialMap

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}
local notation "Aₚ" => Localization.Away (p : A)
local notation "Bₚ" => Localization.Away (p : B)

/-- 基底環射を、既存IsLocalization.mapによってp局所化へ延長する。 -/
def pDivisionFactorialAwayMap (p : ℕ) (f : A →+* B) :
    Localization.Away (p : A) →+* Localization.Away (p : B) :=
  IsLocalization.map (M := Submonoid.powers (p : A)) (T := Submonoid.powers (p : B))
    (Localization.Away (p : B)) f (by
    rintro x ⟨n, rfl⟩
    use n
    simp only [map_pow, map_natCast])

omit [Fact p.Prime] in
/-- p局所化間の実写像は元の基底環射を延長する。 -/
theorem pDivisionFactorialAwayMap_coeff (f : A →+* B) (a : A) :
    pDivisionFactorialAwayMap p f (algebraMap A Aₚ a) = algebraMap B Bₚ (f a) :=
  IsLocalization.map_eq _ _

/-- 源のp局所性の下で、実局所化写像は正規化した階乗分母を保つ。 -/
theorem pDivisionFactorialAwayMap_value (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialAwayMap p f (pDivisionFactorialValue p y s n) =
      pDivisionFactorialValue p (fun s ↦ f (y s)) s n := by
  have hu := DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
    (Nat.factorial_ne_zero n)
  rw [pDivisionFactorialValue, map_mul, hu.map_ringInverse, map_natCast,
    map_pow, pDivisionFactorialAwayMap_coeff]
  rfl

/-- 局所化写像は、具体的な階乗生成部分環を対応する部分環へ写す。 -/
theorem pDivisionFactorialAwayMap_mem (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (t : Aₚ) (ht : t ∈ pDivisionFactorialSubring p y) :
    pDivisionFactorialAwayMap p f t ∈ pDivisionFactorialSubring p (fun s ↦ f (y s)) := by
  have hle : pDivisionFactorialSubring p y ≤
      (pDivisionFactorialSubring p (fun s ↦ f (y s))).comap (pDivisionFactorialAwayMap p f) := by
    apply Subring.closure_le.mpr
    rintro x (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · change pDivisionFactorialAwayMap p f (algebraMap A Aₚ a) ∈
        pDivisionFactorialSubring p (fun s ↦ f (y s))
      rw [pDivisionFactorialAwayMap_coeff]
      exact pDivisionFactorialSubring_coeff_mem _ _
    · change pDivisionFactorialAwayMap p f (pDivisionFactorialValue p y s n) ∈
        pDivisionFactorialSubring p (fun s ↦ f (y s))
      rw [pDivisionFactorialAwayMap_value hlocal]
      exact pDivisionFactorialSubring_value_mem _ s n
  exact hle ht

/-- 基底環射が誘導する、具体的階乗生成部分環間の実環射。 -/
def pDivisionFactorialMap (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    pDivisionFactorialSubring p y →+* pDivisionFactorialSubring p (fun s ↦ f (y s)) :=
  ((pDivisionFactorialAwayMap p f).comp (pDivisionFactorialSubring p y).subtype).codRestrict _
    (fun t ↦ pDivisionFactorialAwayMap_mem hlocal f y t t.property)

/-- 誘導された実環射は、元のAからの基底標準射と可換。 -/
theorem pDivisionFactorialMap_comp_base (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    (pDivisionFactorialMap hlocal f y).comp (pDivisionFactorialBase p y) =
      (pDivisionFactorialBase p (fun s ↦ f (y s))).comp f := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_coeff f a

/-- 誘導された実環射は、各階乗生成元を対応する標準生成元へ送る。 -/
theorem pDivisionFactorialMap_value (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialMap hlocal f y
      ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      ⟨pDivisionFactorialValue p (fun s ↦ f (y s)) s n,
        pDivisionFactorialSubring_value_mem (fun s ↦ f (y s)) s n⟩ := by
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_value hlocal f y s n

/-- 正次数階乗イデアルの像は、対応する標的の正次数階乗イデアルに含まれる。 -/
theorem pDivisionFactorialMap_ideal_le (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (f : A →+* B) (y : σ → A) :
    (pDivisionFactorialIdeal p y).map (pDivisionFactorialMap hlocal f y) ≤
      pDivisionFactorialIdeal p (fun s ↦ f (y s)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro t ⟨⟨s, n⟩, rfl⟩
  change pDivisionFactorialMap hlocal f y _ ∈
    pDivisionFactorialIdeal p (fun s ↦ f (y s))
  rw [pDivisionFactorialMap_value]
  exact Ideal.subset_span (Set.mem_range_self (s, n))

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialMap

/-! ## 具体的階乗生成部分環の射の一意性と関手性 -/

@[expose] public noncomputable section DeltaPDivisionFactorialFunctorial

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type w}

omit [Fact p.Prime] in
/-- 基底と全階乗生成元上で一致する、具体的部分環からの環射は一致する。 -/
theorem pDivisionFactorialHom_ext {T : Type z} [CommRing T] (y : σ → A)
    (F G : pDivisionFactorialSubring p y →+* T)
    (hbase : ∀ a : A, F (pDivisionFactorialBase p y a) = G (pDivisionFactorialBase p y a))
    (hvalue : ∀ (s : σ) (n : ℕ),
      F ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      G ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩) : F = G := by
  apply RingHom.ext
  rintro ⟨t, ht⟩
  induction ht using Subring.closure_induction with
  | mem t ht =>
      rcases ht with (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
      · exact hbase a
      · exact hvalue s n
  | zero => exact (map_zero F).trans (map_zero G).symm
  | one => exact (map_one F).trans (map_one G).symm
  | add x y hx hy ihx ihy =>
      change F (⟨x, hx⟩ + ⟨y, hy⟩) = G (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | neg x hx ih =>
      change F (-⟨x, hx⟩) = G (-⟨x, hx⟩)
      rw [map_neg, map_neg, ih]
  | mul x y hx hy ihx ihy =>
      change F (⟨x, hx⟩ * ⟨y, hy⟩) = G (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

/-- 基底の恒等射が誘導する実階乗部分環射は恒等射。 -/
theorem pDivisionFactorialMap_id (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (y : σ → A) :
    pDivisionFactorialMap hlocal (RingHom.id A) y = RingHom.id (pDivisionFactorialSubring p y) := by
  apply pDivisionFactorialHom_ext y
  · intro a
    exact RingHom.congr_fun (pDivisionFactorialMap_comp_base hlocal (RingHom.id A) y) a
  · intro s n
    exact pDivisionFactorialMap_value hlocal (RingHom.id A) y s n

/-- 基底の合成射が誘導する実階乗部分環射は、誘導射の合成と一致する。 -/
theorem pDivisionFactorialMap_comp {B : Type v} {C : Type z} [CommRing B] [CommRing C]
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (f : A →+* B) (g : B →+* C) (y : σ → A) :
    (pDivisionFactorialMap hB g (fun s ↦ f (y s))).comp (pDivisionFactorialMap hA f y) =
      pDivisionFactorialMap hA (g.comp f) y := by
  apply pDivisionFactorialHom_ext y
  · intro a
    change pDivisionFactorialMap hB g (fun s ↦ f (y s))
        (pDivisionFactorialMap hA f y (pDivisionFactorialBase p y a)) = _
    have hf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA f y) a
    have hg := RingHom.congr_fun (pDivisionFactorialMap_comp_base hB g (fun s ↦ f (y s))) (f a)
    have hgf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA (g.comp f) y) a
    simp only [RingHom.comp_apply] at hf hg hgf
    rw [hf, hg, hgf]
  · intro s n
    change pDivisionFactorialMap hB g (fun s ↦ f (y s))
        (pDivisionFactorialMap hA f y ⟨_, _⟩) = _
    rw [pDivisionFactorialMap_value, pDivisionFactorialMap_value, pDivisionFactorialMap_value]
    rfl

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialFunctorial

/-! ## 具体的階乗部分環の誘導環射の分冪射性

イデアルの全元の全分冪を保つことを階乗の消去で確認する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialDPMorphism

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 基底環射に沿う実誘導環射は、正次数階乗イデアルの全分冪を保つ。 -/
theorem pDivisionFactorialMap_isDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (y : σ → A) :
    DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y)
      (pDivisionFactorialIdealDividedPowers hB E (fun s ↦ f (y s)))
      (pDivisionFactorialMap hA f y) := by
  let g := pDivisionFactorialMap hA f y
  let HA := pDivisionFactorialIdealDividedPowers hA D y
  let HB := pDivisionFactorialIdealDividedPowers hB E (fun s ↦ f (y s))
  let S := pDivisionFactorialSubring p (fun s ↦ f (y s))
  let L := Localization.Away (p : B)
  have hI := pDivisionFactorialMap_ideal_le hA f y
  refine ⟨hI, ?_⟩
  intro n a ha
  have hb : g a ∈ pDivisionFactorialIdeal p (fun s ↦ f (y s)) :=
    hI (Ideal.mem_map_of_mem g ha)
  have he : (n.factorial : S) * HB.dpow n (g a) = (n.factorial : S) * g (HA.dpow n a) := by
    calc
      _ = (g a) ^ n := HB.factorial_mul_dpow_eq_pow hb
      _ = g (a ^ n) := (map_pow g a n).symm
      _ = g ((n.factorial : pDivisionFactorialSubring p y) * HA.dpow n a) :=
        congrArg g (HA.factorial_mul_dpow_eq_pow ha).symm
      _ = _ := by rw [map_mul, map_natCast]
  apply Subtype.ext
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  exact congrArg (fun t : S ↦ (t : L)) he

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialDPMorphism

/-! ## 実階乗部分環の誘導射のδ射性

既存δ局所化の普遍性と、制限したδ作用の具体式を使用する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialDeltaMap

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 基底δ射から誘導された実p局所化写像はδ射。 -/
theorem pDivisionFactorialAwayMap_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (deltaPDivisionAwayStructure D).IsDeltaHom (deltaPDivisionAwayStructure E)
      (pDivisionFactorialAwayMap p f) := by
  let Aₚ := Localization.Away (p : A)
  let Bₚ := Localization.Away (p : B)
  let f₀ := (algebraMap B Bₚ).comp f
  have hu : ∀ s : Submonoid.powers (p : A), IsUnit (f₀ s) := by
    intro s
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) (p : A)).mp s.property
    rw [← hn, map_pow, map_natCast]
    have hp : IsUnit (p : Bₚ) := by
      simpa only [map_natCast] using IsLocalization.Away.algebraMap_isUnit (S := Bₚ) (p : B)
    exact hp.pow n
  obtain ⟨g, hg, _⟩ := D.existsUnique_localization_lift (Submonoid.powers (p : A)) Aₚ
    D.powers_p_frobenius_stable (deltaPDivisionAwayStructure E) f₀
    ((deltaPDivisionAwayStructure_base_isDeltaHom E).comp hf) hu
  have he : g = pDivisionFactorialAwayMap p f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : A))
    apply RingHom.ext
    intro a
    change g (algebraMap A Aₚ a) = pDivisionFactorialAwayMap p f (algebraMap A Aₚ a)
    have h := RingHom.congr_fun hg.1 a
    exact h.trans (pDivisionFactorialAwayMap_coeff f a).symm
  exact he ▸ hg.2

/-- 基底δ射に沿う実階乗部分環射も、既存δ作用の制限を保つ。 -/
theorem pDivisionFactorialMap_isDeltaHom
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B)) (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) (y : σ → A) :
    (pDivisionFactorialDelta hA D y).IsDeltaHom
      (pDivisionFactorialDelta hB E (fun s ↦ f (y s))) (pDivisionFactorialMap hA f y) := by
  intro a
  apply Subtype.ext
  exact pDivisionFactorialAwayMap_isDeltaHom D E f hf (a : Localization.Away (p : A))

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialDeltaMap

/-! ## 既存分冪イデアルを持つ標的における階乗部分環

分冪の階乗恒等式で具体的部分環を基底の像へ同定する。
像の同定はpねじれを許す。環同型の構成時のみp正則性を要求する。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialPDTarget

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 分冪イデアル内の元の階乗分母は、実分冪値の局所化像である。 -/
theorem pDivisionFactorialValue_eq_dpow_image
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I)
    (s : σ) (n : ℕ) :
    pDivisionFactorialValue p y s n =
      algebraMap A (Localization.Away (p : A)) (H.dpow n (y s)) := by
  have h := congrArg (algebraMap A (Localization.Away (p : A)))
    (H.factorial_mul_dpow_eq_pow (n := n) (hy s))
  simp only [map_mul, map_natCast, map_pow] at h
  rw [pDivisionFactorialValue, ← h, Ring.inverse_mul_cancel_left _ _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hlocal n.factorial
      (Nat.factorial_ne_zero n))]

/-- 既に分冪イデアル内にある元族を添加しても、局所化内では基底の像に留まる。 -/
theorem pDivisionFactorialSubring_eq_baseRange
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    pDivisionFactorialSubring p y = (algebraMap A (Localization.Away (p : A))).range := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro t (⟨a, rfl⟩ | ⟨⟨s, n⟩, rfl⟩)
    · exact ⟨a, rfl⟩
    · exact ⟨H.dpow n (y s), (pDivisionFactorialValue_eq_dpow_image hlocal H y hy s n).symm⟩
  · rintro t ⟨a, rfl⟩
    exact pDivisionFactorialSubring_coeff_mem y a

/-- 分冪標的に対する基底射は、pねじれがあっても全射。 -/
theorem pDivisionFactorialBase_surjective_of_dividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    Function.Surjective (pDivisionFactorialBase p y) := by
  rintro ⟨t, ht⟩
  rw [pDivisionFactorialSubring_eq_baseRange hlocal H y hy] at ht
  obtain ⟨a, ha⟩ := ht
  exact ⟨a, Subtype.ext ha⟩

omit [Fact p.Prime] in
/-- p正則な基底では、階乗部分環への基底射も単射。 -/
theorem pDivisionFactorialBase_injective
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a)) (y : σ → A) :
    Function.Injective (pDivisionFactorialBase p y) := by
  have hi : Function.Injective (algebraMap A (Localization.Away (p : A))) := by
    apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : A))
      (S := Localization.Away (p : A))).mpr
    intro c
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : A) (p : A)).mp c.property
    have hr : IsRegular (p : A) := ⟨hpA, by
      intro x z h
      apply hpA
      simpa only [mul_comm] using h⟩
    rw [← hn]
    exact hr.pow n
  intro x z h
  apply hi
  exact congrArg Subtype.val h

/-- p正則な既存分冪標的では、基底射自身が具体的階乗部分環との環同型を与える。 -/
def pDivisionFactorialBaseEquivOfDividedPowers
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
    {I : Ideal A} (H : DividedPowers I) (y : σ → A) (hy : ∀ s, y s ∈ I) :
    A ≃+* pDivisionFactorialSubring p y :=
  RingEquiv.ofBijective (pDivisionFactorialBase p y)
    ⟨pDivisionFactorialBase_injective hpA y,
      pDivisionFactorialBase_surjective_of_dividedPowers hlocal H y hy⟩

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialPDTarget

/-! ## p正則な分冪標的への具体的階乗部分環の延長射

標的のp正則性を明示する。pねじれのある一般分冪標的の普遍性は主張しない。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialPDLift

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 具体的部分環内でも、階乗を掛けると元の通常冪に戻る。 -/
theorem pDivisionFactorialValue_factorial_mul
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A)) (y : σ → A) (s : σ) (n : ℕ) :
    (n.factorial : pDivisionFactorialSubring p y) *
        ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      pDivisionFactorialBase p y (y s) ^ n := by
  apply Subtype.ext
  change (n.factorial : Localization.Away (p : A)) *
    (Ring.inverse (n.factorial : Localization.Away (p : A)) * _) = _
  rw [← mul_assoc, Ring.mul_inverse_cancel _
    (DeltaStructure.primeDividedPowersAwayNat_isUnit hA n.factorial
      (Nat.factorial_ne_zero n)), one_mul]
  rfl

/-- 基底射を延長する、p正則分冪標的への実環射。 -/
def pDivisionFactorialLiftToPDTarget
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) : pDivisionFactorialSubring p y →+* B :=
  (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm.toRingHom.comp
    (pDivisionFactorialMap hA f y)

/-- 実延長射は指定された基底射を延長する。 -/
theorem pDivisionFactorialLiftToPDTarget_comp_base
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy).comp
      (pDivisionFactorialBase p y) = f := by
  ext a
  change (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm
    (pDivisionFactorialMap hA f y (pDivisionFactorialBase p y a)) = f a
  have hf := RingHom.congr_fun (pDivisionFactorialMap_comp_base hA f y) a
  simp only [RingHom.comp_apply] at hf
  rw [hf]
  exact (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H
    (fun s ↦ f (y s)) hy).symm_apply_apply (f a)

/-- 実延長射は全階乗生成元を指定の分冪値へ送る。 -/
theorem pDivisionFactorialLiftToPDTarget_value
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) (s : σ) (n : ℕ) :
    pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy
      ⟨pDivisionFactorialValue p y s n, pDivisionFactorialSubring_value_mem y s n⟩ =
      H.dpow n (f (y s)) := by
  change (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).symm
    (pDivisionFactorialMap hA f y _) = _
  rw [pDivisionFactorialMap_value]
  apply (pDivisionFactorialBaseEquivOfDividedPowers hB hpB H (fun s ↦ f (y s)) hy).injective
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  exact pDivisionFactorialValue_eq_dpow_image hB H (fun s ↦ f (y s)) hy s n

/-- p正則な標的への環射は、基底上の値のみで一意に決まる。 -/
theorem pDivisionFactorialHom_ext_of_p_regular
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b)) (y : σ → A)
    (F G : pDivisionFactorialSubring p y →+* B)
    (hbase : ∀ a : A, F (pDivisionFactorialBase p y a) = G (pDivisionFactorialBase p y a)) :
    F = G := by
  apply pDivisionFactorialHom_ext y F G hbase
  intro s n
  let g : B →+* Localization.Away (p : B) := algebraMap B _
  have hi : Function.Injective g := by
    intro x z h
    exact pDivisionFactorialBase_injective hpB (fun _ : Unit ↦ (0 : B)) (Subtype.ext h)
  apply hi
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  have hF := congrArg F (pDivisionFactorialValue_factorial_mul hA y s n)
  have hG := congrArg G (pDivisionFactorialValue_factorial_mul hA y s n)
  simp only [map_mul, map_natCast, map_pow] at hF hG
  rw [hbase] at hF
  simpa only [map_mul, map_natCast] using congrArg g (hF.trans hG.symm)

/-- p正則な分冪標的への、指定の基底射を延長する環射の存在と一意性。 -/
theorem existsUnique_pDivisionFactorialLiftToPDTarget
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    ∃! F : pDivisionFactorialSubring p y →+* B, F.comp (pDivisionFactorialBase p y) = f := by
  refine ⟨pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy,
    pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy, ?_⟩
  intro F hF
  apply pDivisionFactorialHom_ext_of_p_regular hA hB hpB y
  intro a
  exact (RingHom.congr_fun hF a).trans
    (RingHom.congr_fun (pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy) a).symm

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialPDLift

/-! ## p正則な分冪標的に対する分冪射の普遍性

具体的階乗部分環と正次数イデアルを使用する。標的のp正則性を明示する。
一般の分冪包や導来比較の構築は含まない。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialPDUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {σ : Type w}

/-- 実延長射は正次数階乗イデアルを指定された分冪イデアルへ写す。 -/
theorem pDivisionFactorialLiftToPDTarget_ideal_le
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    {I : Ideal B} (H : DividedPowers I) (f : A →+* B) (y : σ → A)
    (hy : ∀ s, f (y s) ∈ I) :
    (pDivisionFactorialIdeal p y).map
      (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy) ≤ I := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨s, n⟩, rfl⟩
  change pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy _ ∈ I
  rw [pDivisionFactorialLiftToPDTarget_value]
  exact H.dpow_mem (Nat.succ_ne_zero n) (hy s)

/-- 任意のp正則分冪標的への実延長射は全分冪を保つ。 -/
theorem pDivisionFactorialLiftToPDTarget_isDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    (D : DeltaStructure p A) {I : Ideal B} (H : DividedPowers I)
    (f : A →+* B) (y : σ → A) (hy : ∀ s, f (y s) ∈ I) :
    DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y) H
      (pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy) := by
  let g := pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy
  let HA := pDivisionFactorialIdealDividedPowers hA D y
  have hI := pDivisionFactorialLiftToPDTarget_ideal_le hA hB hpB H f y hy
  refine ⟨hI, ?_⟩
  intro n a ha
  have hb : g a ∈ I := hI (Ideal.mem_map_of_mem g ha)
  have he : (n.factorial : B) * H.dpow n (g a) = (n.factorial : B) * g (HA.dpow n a) := by
    calc
      _ = (g a) ^ n := H.factorial_mul_dpow_eq_pow hb
      _ = g (a ^ n) := (map_pow g a n).symm
      _ = g ((n.factorial : pDivisionFactorialSubring p y) * HA.dpow n a) :=
        congrArg g (HA.factorial_mul_dpow_eq_pow ha).symm
      _ = _ := by rw [map_mul, map_natCast]
  have hi : Function.Injective (algebraMap B (Localization.Away (p : B))) := by
    intro x z h
    exact pDivisionFactorialBase_injective hpB (fun _ : Unit ↦ (0 : B)) (Subtype.ext h)
  apply hi
  apply (DeltaStructure.primeDividedPowersAwayNat_isUnit hB n.factorial
    (Nat.factorial_ne_zero n)).mul_left_cancel
  simpa only [map_mul, map_natCast] using
    congrArg (algebraMap B (Localization.Away (p : B))) he

/-- p正則な分冪標的に対し、基底射を延長する分冪射が一意に存在する。 -/
theorem existsUnique_pDivisionFactorialDPMorphism
    (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
    (hB : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : B))
    (hpB : Function.Injective (fun b : B ↦ (p : B) * b))
    (D : DeltaStructure p A) {I : Ideal B} (H : DividedPowers I)
    (f : A →+* B) (y : σ → A) (hy : ∀ s, f (y s) ∈ I) :
    ∃! F : pDivisionFactorialSubring p y →+* B,
      F.comp (pDivisionFactorialBase p y) = f ∧
        DividedPowers.IsDPMorphism (pDivisionFactorialIdealDividedPowers hA D y) H F := by
  refine ⟨pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy,
    ⟨pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy,
      pDivisionFactorialLiftToPDTarget_isDPMorphism hA hB hpB D H f y hy⟩, ?_⟩
  intro F hF
  exact (existsUnique_pDivisionFactorialLiftToPDTarget hA hB hpB H f y hy).unique hF.1
    (pDivisionFactorialLiftToPDTarget_comp_base hA hB hpB H f y hy)

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialPDUniversal

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Warning 2.41" (partial := special) "前半（部分環 A{φ(f)/p} ⊂ A[1/p] が δ 構造によらない）は一般形で本体にある。捻りなしの部分環が δ 構造による反例（R₁, R₂）はない ／ 11-12 夜更新（§2 の見直し）"] _root_.SerrePositivity.BhattScholze.deltaPDivisionToAway_range_eq_of_deltaStructure
