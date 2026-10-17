module

public import SerrePositivity.BhattScholze.Andre.PrincipalDPPositiveUniversal

/-!
# André E1・E2：係数還元後の実 pd 包の普遍性

## 概要

一次関係商のさらに商 Q が実分冪構造を持ち、入力の分冪が標準生成元の商像なら、
関係式を殺す任意の分冪標的への係数を保つ分冪射は一意に存在する。
BS Rem 7.15(1)（著者版 p.62）の係数変更後の実 pd 包を扱う。

## 方針

通常の分冪評価を商へ降ろし、正次数生成元上の分冪合成公式で互換性を示す。
一意性は元の一次関係商の生成元による外延性を使う。

## 規約

商の分冪構造と入力値の公式は明示引数。標的の正則性・標数は要求しない。

## 使われ方

正則係数元による実分冪降下と組み合わせ、降下後の pd 普遍性を証明する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
local notation "D" => PrincipalDPPresentation A y
variable (K : Ideal (PrincipalDPPresentation A y))
local notation "q" => Ideal.Quotient.mk K
local notation "Q" => D ⧸ K
local notation "J" => Ideal.map q (principalDPPositiveIdeal y)
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (Ht : DividedPowers I) (hyB : algebraMap A B y ∈ I)
variable (hK : ∀ t ∈ K, principalDPEval Ht y hyB t = 0)

/-- 概要：標準分冪評価は関係式を殺すなら実商からの射へ降りる。
方針：通常の代数商の普遍射を使う。
規約：関係式は任意のイデアル K で指定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数還元後の評価。 -/
def principalDPQuotientEval : Q →ₐ[A] B :=
  Ideal.Quotient.liftₐ K (principalDPEval Ht y hyB) hK

/-- 概要：商の評価は代表元で元の標準評価に一致する。
方針：商の普遍射の定義を使う。
規約：元の一次関係商の任意の元を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の射の比較。 -/
theorem principalDPQuotientEval_mk (t : D) :
    principalDPQuotientEval y K Ht hyB hK (q t) = principalDPEval Ht y hyB t := rfl

/-- 概要：商の標準生成元の評価は標的の入力元の分冪。
方針：代表元公式と元の評価公式を使う。
規約：全次数を扱う。
使われ方：BS Rem 7.15(1)（著者版 p.62）の分冪射の判定。 -/
theorem principalDPQuotientEval_generator (n : ℕ) :
    principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y n)) =
      Ht.dpow n (algebraMap A B y) := by
  rw [principalDPQuotientEval_mk, principalDPEval_generator]

variable (Hq : DividedPowers ((principalDPPositiveIdeal y).map (Ideal.Quotient.mk K)))
variable (hγ : ∀ n, Hq.dpow n
  (Ideal.Quotient.mk K (algebraMap A (PrincipalDPPresentation A y) y)) =
    Ideal.Quotient.mk K (principalDPGenerator y n))

include hγ in
/-- 概要：商の標準評価は実分冪構造を保つ。
方針：像イデアルの正次数生成元で分冪合成則を照合する。
規約：商の構造と標準値の公式だけを仮定する。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実商からの pd 普遍射。 -/
theorem principalDPQuotientEval_isDPMorphism :
    Hq.IsDPMorphism Ht (principalDPQuotientEval y K Ht hyB hK).toRingHom := by
  have hbase : q (algebraMap A D y) ∈ J :=
    Ideal.mem_map_of_mem q (principalDPPositiveIdeal_base_mem y)
  have hspan : J = Ideal.span (Set.range fun k : ℕ => q (principalDPGenerator y (k + 1))) := by
    rw [principalDPPositiveIdeal, Ideal.map_span, ← Set.range_comp']
  apply DividedPowers.IsDPMorphism.on_span Hq Ht hspan
  · rintro t ⟨k, rfl⟩
    change principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y (k + 1))) ∈ I
    rw [principalDPQuotientEval_generator]
    exact Ht.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n t ⟨k, rfl⟩
    change principalDPQuotientEval y K Ht hyB hK
      (Hq.dpow n (q (principalDPGenerator y (k + 1)))) =
        Ht.dpow n (principalDPQuotientEval y K Ht hyB hK
          (q (principalDPGenerator y (k + 1))))
    rw [← hγ (k + 1), Hq.dpow_comp (Nat.succ_ne_zero k) hbase, map_mul,
      map_natCast, hγ (n * (k + 1)), hγ (k + 1), principalDPQuotientEval_generator,
      principalDPQuotientEval_generator, Ht.dpow_comp (Nat.succ_ne_zero k) hyB]

include hγ hyB hK in
/-- 概要：関係式を殺す任意の分冪標的への係数を保つ分冪射は一意に存在する。
方針：商の標準評価で存在を示し、入力元の分冪から全生成元上の一致を得る。
規約：標的にねじれなし等の追加仮定を置かない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の係数変更後の pd 普遍性。 -/
theorem existsUnique_principalDPQuotientMorphism :
    ∃! F : Q →ₐ[A] B, Hq.IsDPMorphism Ht F.toRingHom := by
  refine ⟨principalDPQuotientEval y K Ht hyB hK,
    principalDPQuotientEval_isDPMorphism y K Ht hyB hK Hq hγ, ?_⟩
  intro F hF
  apply Ideal.Quotient.algHom_ext
  apply principalDPHom_ext
  intro n
  change F (q (principalDPGenerator y n)) =
    principalDPQuotientEval y K Ht hyB hK (q (principalDPGenerator y n))
  rw [principalDPQuotientEval_generator]
  calc
    F (q (principalDPGenerator y n)) =
        F.toRingHom (Hq.dpow n (q (algebraMap A D y))) := congrArg F (hγ n).symm
    _ = Ht.dpow n (F (q (algebraMap A D y))) :=
      (hF.dpow_comp _ (Ideal.mem_map_of_mem q (principalDPPositiveIdeal_base_mem y))).symm
    _ = Ht.dpow n (algebraMap A B y) := by
      change Ht.dpow n (F (algebraMap A Q y)) = _
      rw [F.commutes]


end SerrePositivity.BhattScholze.Andre
