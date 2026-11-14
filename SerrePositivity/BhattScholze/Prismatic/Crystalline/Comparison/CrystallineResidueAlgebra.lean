module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 分冪剰余代数の基底環上の構造

## 概要
k/J 代数を k 代数として読み、J が零に写ることを確認する。

## 方針
商写像と代数の構造射を合成する。

## 規約
選択に依らない明示的な環射を使う。

## 使われ方
Berthelot III.4、Stacks 07HM。分冪枠の評価と結晶厚化の構造射の接続。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable {k : Type u} [CommRing k] {J : Ideal k}
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]

/-- 剰余代数を、商写像を通して基底環の代数として読む。 -/
abbrev crysResidueAlgebra : Algebra k R :=
  ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)).toAlgebra

/-- 基底の分冪イデアルは剰余代数で零になる。 -/
theorem crysResidue_kernel :
    letI := crysResidueAlgebra (J := J) R
    J ≤ RingHom.ker (algebraMap k R) := by
  intro x hx
  change algebraMap (k ⧸ J) R (Ideal.Quotient.mk J x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

/-- 既に指定した係数構造が剰余を経由する場合にも、J は零になる。 -/
theorem crysResidue_kernel_of_tower [Algebra k R] [IsScalarTower k (k ⧸ J) R] :
    J ≤ RingHom.ker (algebraMap k R) := by
  intro x hx
  change algebraMap k R x = 0
  rw [IsScalarTower.algebraMap_apply k (k ⧸ J) R]
  change algebraMap (k ⧸ J) R (Ideal.Quotient.mk J x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end SerrePositivity.BhattScholze.Prismatic
