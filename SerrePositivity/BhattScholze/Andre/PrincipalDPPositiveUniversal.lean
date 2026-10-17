module

public import SerrePositivity.BhattScholze.Andre.RegularPrincipalModPrimeDividedPowers

/-!
# André E1・E2：正次数分冪構造を持つ一次関係商の実普遍性

## 概要

一次関係商の入力元の分冪が全標準生成元と一致するなら、任意の分冪標的へ
係数を保つ分冪射が一意に存在する。BS Rem 7.15(1)（著者版 p.62）の pd 包の普遍性。

## 方針

既存の通常代数の評価射が分冪射であることを正次数生成元上で確認する。
一意性は全標準生成元上の外延性に帰着する。

## 規約

分冪構造と入力元の値の公式を明示引数にする。実構造の存在は前工程で別に証明する。
標的のねじれ・正則性・δ 構造は要求しない。

## 使われ方

正則な δ 持ち上げから得た実 mod p 分冪構造を、pd 包の普遍性と結び付ける。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] (y : A)
variable (Hs : DividedPowers (principalDPPositiveIdeal y))
variable (hγ : ∀ n, Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y) =
  principalDPGenerator y n)
variable {B : Type v} [CommRing B] [Algebra A B] {I : Ideal B}
variable (Ht : DividedPowers I) (hyB : algebraMap A B y ∈ I)

include hγ hyB

/-- 概要：一次関係商の標準評価は実際の分冪射である。
方針：正次数生成元上で分冪の合成則と入力元の値の公式を比較する。
規約：標的には任意の p ねじれを許し、素数も指定しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の pd 包の存在側の普遍射。 -/
theorem principalDPEval_positive_isDPMorphism :
    Hs.IsDPMorphism Ht (principalDPEval Ht y hyB).toRingHom := by
  have hbase := principalDPPositiveIdeal_base_mem y
  apply DividedPowers.IsDPMorphism.on_span Hs Ht
    (S := Set.range fun k : ℕ => principalDPGenerator y (k + 1)) rfl
  · rintro a ⟨k, rfl⟩
    change principalDPEval Ht y hyB (principalDPGenerator y (k + 1)) ∈ I
    rw [principalDPEval_generator]
    exact Ht.dpow_mem (Nat.succ_ne_zero k) hyB
  · rintro n a ⟨k, rfl⟩
    change principalDPEval Ht y hyB (Hs.dpow n (principalDPGenerator y (k + 1))) =
      Ht.dpow n (principalDPEval Ht y hyB (principalDPGenerator y (k + 1)))
    rw [← hγ (k + 1), Hs.dpow_comp (Nat.succ_ne_zero k) hbase, map_mul, map_natCast,
      hγ (n * (k + 1)), hγ (k + 1), principalDPEval_generator, principalDPEval_generator,
      Ht.dpow_comp (Nat.succ_ne_zero k) hyB]

/-- 概要：一次関係商から任意の分冪標的への係数を保つ分冪射は一意に存在する。
方針：標準評価を存在証人とし、入力元の分冪値から全標準生成元上の一致を得る。
規約：構造と値の公式を前提にし、標的には追加の正則性を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実 pd 包の普遍性。 -/
theorem existsUnique_principalDPPositiveMorphism :
    ∃! F : PrincipalDPPresentation A y →ₐ[A] B, Hs.IsDPMorphism Ht F.toRingHom := by
  refine ⟨principalDPEval Ht y hyB, principalDPEval_positive_isDPMorphism y Hs hγ Ht hyB, ?_⟩
  intro F hF
  apply principalDPHom_ext
  intro n
  calc
    F (principalDPGenerator y n) =
        F (Hs.dpow n (algebraMap A (PrincipalDPPresentation A y) y)) := congrArg F (hγ n).symm
    _ = Ht.dpow n (F (algebraMap A (PrincipalDPPresentation A y) y)) :=
      (hF.dpow_comp _ (principalDPPositiveIdeal_base_mem y)).symm
    _ = Ht.dpow n (algebraMap A B y) := congrArg (Ht.dpow n) (F.commutes y)
    _ = _ := (principalDPEval_generator Ht y hyB n).symm

end SerrePositivity.BhattScholze.Andre
