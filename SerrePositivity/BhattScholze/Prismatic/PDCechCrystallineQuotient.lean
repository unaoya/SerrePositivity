module

public import SerrePositivity.BhattScholze.Prismatic.PDCechResidueEquivalence
public import SerrePositivity.BhattScholze.Prismatic.CrystallineResidueAlgebra
public import SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve

/-!
# 分冪 Čech 包の有限冪商を結晶厚化にする

## 概要
全射な枠の各分冪 Čech 項を p^{e+2} で割り、剰余代数上の結晶厚化を得る。

## 方針
分冪包の剰余同型の逆で構造射を固定し、一般の有限 p 冪商の構成を適用する。

## 規約
分冪包の各項の濃度の上限を明示する。一般基底での分冪の降下のため指数は e+2。

## 使われ方
Berthelot III.4、Stacks 07HP。結晶サイトの pd Čech の塔の対象。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
local notation "hJ" => crysResidue_kernel_of_tower (J := J) R
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
local notation "D" n => PDCechNerve.term p γ hp hJ s n

/-- 分冪包の剰余への、元の剰余代数からの標準構造射。 -/
def pdCechResidueSection (n : ℕ) : R →+* (D n).carrier ⧸ (D n).ideal :=
  (crystallineCechResidueEquiv p γ hp hJ s hs n).symm.toRingHom

/-- 剰余構造射は基底の係数と両立する。 -/
theorem pdCechResidueSection_base (n : ℕ) :
    (pdCechResidueSection p γ hp R s hs n).comp
      ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
        (Ideal.Quotient.mk (D n).ideal).comp (algebraMap k (D n).carrier) := by
  ext a
  change (crystallineCechResidueEquiv p γ hp hJ s hs n).symm
    (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a)) = _
  have ha : algebraMap k R a = algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a) :=
    IsScalarTower.algebraMap_apply k (k ⧸ J) R a
  rw [← ha]
  exact (crystallineCechResidueEquiv p γ hp hJ s hs n).symm.commutes a

/-- p は各 Čech 項の分冪イデアルに属する。 -/
theorem pdCechPrime_mem (n : ℕ) : (p : (D n).carrier) ∈ (D n).ideal := by
  simpa only [map_natCast] using
    (D n).isEnvelope.base_dp.ideal_comp (Ideal.mem_map_of_mem _ hp)

/-- 分冪 Čech 包の有限冪商からなる、結晶サイトの実際の対象。 -/
def pdCechQuotient {κ : Cardinal.{u}} (hsmall : ∀ n, Cardinal.mk (D n).carrier ≤ κ)
    (e n : ℕ) : CrysOver p γ R κ :=
  crystallinePDQuotient p γ R (D n).dividedPowers (pdCechPrime_mem p γ hp R s n)
    (D n).isEnvelope.base_dp (pdCechResidueSection p γ hp R s hs n)
    (pdCechResidueSection_base p γ hp R s hs n) (hsmall n) e

end SerrePositivity.BhattScholze.Prismatic
