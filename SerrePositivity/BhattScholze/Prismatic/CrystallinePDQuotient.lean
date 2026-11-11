module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineResidue
public import SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion
import all SerrePositivity.BhattScholze.Prismatic.PDAdicCompletion

/-!
# 分冪環の有限 p 冪商を結晶厚化として読む

## 概要
剰余代数の構造射を持つ分冪環から、p 冪零な結晶厚化を構成する。

## 方針
既存の分冪部分イデアル p^{e+2} で割り、イデアルと分冪を降ろす。

## 規約
指数を e+2 から取ることで、一般の基底で γ_n(p) の追加の可除性を仮定せずに
分冪の降下を保証する。台環の濃度の上限は明示する。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪 Čech 包の有限冪商の塔。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable {D : Type u} [CommRing D] [Algebra k D] {I : Ideal D} (δ : DividedPowers I)
variable (hp : (p : D) ∈ I) (hbase : DividedPowers.IsDPMorphism γ δ (algebraMap k D))
variable (sec : R →+* D ⧸ I)
variable (hsec : sec.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
  (Ideal.Quotient.mk I).comp (algebraMap k D))
variable {κ : Cardinal.{u}} (hsmall : Cardinal.mk D ≤ κ)
local notation "P" => Ideal.span {(p : D)}

/-- 元の分冪剰余から有限冪商の分冪剰余への標準射。 -/
def crystallineQuotientResidueMap (e : ℕ) :
    D ⧸ I →+* (D ⧸ (P ^ (e + 2))) ⧸ I.map (Ideal.Quotient.mk (P ^ (e + 2))) :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) Ideal.le_comap_map

/-- 有限 p 冪商で分冪を降ろした結晶厚化。 -/
def crystallinePDQuotient (e : ℕ) : CrysOver p γ R κ where
  B := D ⧸ (P ^ (e + 2))
  JB := I.map (Ideal.Quotient.mk (P ^ (e + 2)))
  δ := PDAdicCompletion.quotientDividedPowers p δ hp e
  base_dp := by
    have hq : δ.IsDPMorphism (PDAdicCompletion.quotientDividedPowers p δ hp e)
        (Ideal.Quotient.mk (P ^ (e + 2))) :=
      DividedPowers.Quotient.isDPMorphism _ _
    have hc := hq.comp _ hbase
    convert hc using 1
  nilpotent := by
    refine ⟨e + 2, ?_⟩
    change (Ideal.Quotient.mk (P ^ (e + 2)) (p : D)) ^ (e + 2) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : D)) _
  sec := (crystallineQuotientResidueMap p e).comp sec
  sec_comp := by
    ext a
    change crystallineQuotientResidueMap p e
      (sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a))) = _
    rw [show sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a)) =
      Ideal.Quotient.mk I (algebraMap k D a) from DFunLike.congr_fun hsec a]
    rfl
  small := (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans hsmall

end SerrePositivity.BhattScholze.Prismatic
