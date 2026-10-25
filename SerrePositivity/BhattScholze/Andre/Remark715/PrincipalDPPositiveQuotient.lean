module

public import SerrePositivity.BhattScholze.Andre.Remark715.RegularPrincipalModPrimeDividedPowers

/-!
# André E1・E2：正次数分冪イデアルによる商と元の入力商

## 概要

γ₁=y の一元分冪表示環を全正次数生成元のイデアルで割ると A/(y) に A 代数同型。
BS Rem 7.15(1)（著者版 p.62）の係数変更で実分冪構造を降ろすための計算。

## 方針

零イデアルの分冪構造への評価で augmentation を構成し、係数からの逆射を作る。
逆合成は係数と全標準生成元上で確認する。

## 規約

係数環の標数・正則性・非零性も、表示環自身の分冪構造も要求しない。

## 使われ方

モニック入力商の自由性から正次数イデアルによる商の平坦性を得て、係数変更を制御する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
local notation "D" => PrincipalDPPresentation A y
local notation "J" => principalDPPositiveIdeal y
local notation "R" => A ⧸ Ideal.span {(y : A)}

/-- 概要：入力 y の係数像は実入力商 A/(y) で零。
方針：入力元が定義の主イデアルに属することを使う。
規約：標準の係数商射を使用する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の augmentation の入力。 -/
theorem principalDPInputQuotient_input_eq_zero : algebraMap A R y = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)

/-- 概要：一次関係商から元の入力商への augmentation。
方針：標的の零イデアルの分冪構造へ標準評価する。
規約：係数環 A の作用を保持する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数商の同定。 -/
def principalDPAugmentation : D →ₐ[A] R :=
  principalDPEval (dividedPowersBot R) y
    (Ideal.mem_bot.mpr (principalDPInputQuotient_input_eq_zero y))

/-- 概要：augmentation は全正次数標準生成元を零へ送る。
方針：零イデアル内の正次数分冪は零であることを使う。
規約：次数は n+1 とする。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正次数商への降下。 -/
theorem principalDPAugmentation_generator_succ (n : ℕ) :
    principalDPAugmentation y (principalDPGenerator y (n + 1)) = 0 := by
  rw [principalDPAugmentation, principalDPEval_generator]
  exact Ideal.mem_bot.mp ((dividedPowersBot R).dpow_mem (Nat.succ_ne_zero n)
    (Ideal.mem_bot.mpr (principalDPInputQuotient_input_eq_zero y)))

/-- 概要：augmentation は正次数イデアルによる商から入力商へ降りる。
方針：正次数生成元を全て零に送るので商の普遍射を使う。
規約：実際の正次数イデアル J の商を取る。
使われ方：BS Rem 7.15(1)（著者版 p.62）の商同型の順射。 -/
def principalDPPositiveQuotientToInput : (D ⧸ J) →ₐ[A] R := by
  apply Ideal.Quotient.liftₐ _ (principalDPAugmentation y)
  have hker : J ≤ RingHom.ker (principalDPAugmentation y).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact principalDPAugmentation_generator_succ y n
  exact fun _ hx => hker hx

/-- 概要：正次数商からの augmentation は代表元で元の augmentation と一致。
方針：商の普遍射の代表元公式を使う。
規約：全ての表示環の元で述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の逆合成の検証。 -/
theorem principalDPPositiveQuotientToInput_mk (x : D) :
    principalDPPositiveQuotientToInput y (Ideal.Quotient.mk J x) =
      principalDPAugmentation y x := rfl

/-- 概要：入力商 A/(y) から正次数分冪商への標準係数射。
方針：入力 y が正次数イデアルに属すので係数射を入力商へ降ろす。
規約：元の A 係数作用を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の商同型の逆射。 -/
def principalDPInputToPositiveQuotient : R →ₐ[A] D ⧸ J := by
  apply Ideal.Quotient.liftₐ _ (Algebra.ofId A (D ⧸ J))
  have hker : Ideal.span {y} ≤ RingHom.ker (Algebra.ofId A (D ⧸ J)).toRingHom := by
    apply Ideal.span_le.mpr
    intro t ht
    have hty : t = y := Set.mem_singleton_iff.mp ht
    subst t
    change Ideal.Quotient.mk J (algebraMap A D y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (principalDPPositiveIdeal_base_mem y)
  exact fun _ hx => hker hx

/-- 概要：入力商からの標準射は元の係数を同じ正次数商の係数へ送る。
方針：商への降下の定義を使う。
規約：任意の元 a の商代表元で述べる。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数上の逆合成。 -/
theorem principalDPInputToPositiveQuotient_mk (a : A) :
    principalDPInputToPositiveQuotient y (Ideal.Quotient.mk _ a) = algebraMap A (D ⧸ J) a := rfl

/-- 概要：入力商から正次数商へ移して戻すと恒等射。
方針：入力商の係数代表元上で代数射の可換性を使う。
規約：係数環 A を固定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の商同型の検証。 -/
theorem principalDPPositiveQuotientToInput_comp_inputToPositive :
    (principalDPPositiveQuotientToInput y).comp (principalDPInputToPositiveQuotient y) =
      AlgHom.id A R := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro a
  change principalDPPositiveQuotientToInput y
    (principalDPInputToPositiveQuotient y (Ideal.Quotient.mk _ a)) = _
  rw [principalDPInputToPositiveQuotient_mk, AlgHom.commutes]
  rfl

/-- 概要：正次数商から入力商へ移して戻しても恒等射。
方針：零次生成元は単位、正次数生成元は両側とも零であることを使う。
規約：表示環の全標準生成元上で確認する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の商同型の検証。 -/
theorem principalDPInputToPositiveQuotient_comp_positiveToInput :
    (principalDPInputToPositiveQuotient y).comp (principalDPPositiveQuotientToInput y) =
      AlgHom.id A (D ⧸ J) := by
  apply Ideal.Quotient.algHom_ext
  apply principalDPHom_ext
  intro n
  cases n with
  | zero => simp [principalDPGenerator, DividedPowerAlgebra.dp_zero]
  | succ n =>
    change principalDPInputToPositiveQuotient y
      (principalDPPositiveQuotientToInput y
        (Ideal.Quotient.mk J (principalDPGenerator y (n + 1)))) =
        Ideal.Quotient.mk J (principalDPGenerator y (n + 1))
    rw [principalDPPositiveQuotientToInput_mk, principalDPAugmentation_generator_succ, map_zero]
    symm
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self n))

/-- 概要：一次関係商を正次数分冪イデアルで割ると元の入力商 A/(y) と A 代数同型。
方針：互いに逆と確認した augmentation と係数射を束ねる。
規約：係数環の標数や正則性は要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更での平坦性とイデアル交わりの制御。 -/
def principalDPPositiveQuotientEquiv : (D ⧸ J) ≃ₐ[A] R :=
  AlgEquiv.ofAlgHom (principalDPPositiveQuotientToInput y) (principalDPInputToPositiveQuotient y)
    (principalDPPositiveQuotientToInput_comp_inputToPositive y)
    (principalDPInputToPositiveQuotient_comp_positiveToInput y)

end SerrePositivity.BhattScholze.Andre
