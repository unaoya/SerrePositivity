module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLift
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineQuotient
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientTower
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteSmall
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineFrameLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechResidueEquivalence
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientTower

/-!
# 分冪 Čech 零次の塔の pro 弱終性

## 概要
全射な枠の分冪包の有限 p 冪商の塔は、結晶サイトで pro 弱終である。

## 方針
任意の厚化へ枠の変数を持ち上げ、完備分冪包からの射を標的の p 冪零指数で降ろす。

## 規約
分冪包の濃度が cutoff に入ることを明示的な仮定に取る。

## 使われ方
BS 著者版 Theorem 5.2、Berthelot III.4、Stacks 07HP。pd Čech の塔の零次。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
local notation "hJ" => crysResidue_kernel_of_tower (J := J) R
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
local notation "D" => PDCechNerve.term p γ hp hJ s 0

/-- 枠の持ち上げが、包の剰余の標準構造射を保つことの商環での式。 -/
theorem crystallineFrameLift_comp_residueSection {κ : Cardinal.{u}}
    (X : CrysOver p γ R κ) :
    (Ideal.quotientMap X.JB (crystallineFrameLift X s hp 0).toRingHom
      (Ideal.map_le_iff_le_comap.mp (crystallineFrameLift_dp X s hp 0).ideal_comp)).comp
        (pdCechResidueSection p γ hp R s hs 0) = X.sec := by
  ext r
  let E := crystallineCechResidueEquiv p γ hp hJ s hs 0
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (pdCechResidueSection p γ hp R s hs 0 r)
  have he : PDCechNerve.augmentation p γ hp hJ s 0 b = r := by
    rw [← crystallineCechResidueEquiv_mk p γ hp hJ s hs 0 b, hb]
    exact E.apply_symm_apply r
  change (Ideal.quotientMap (I := (D).ideal) X.JB
    (crystallineFrameLift X s hp 0).toRingHom
      (Ideal.map_le_iff_le_comap.mp (crystallineFrameLift_dp X s hp 0).ideal_comp))
      (pdCechResidueSection p γ hp R s hs 0 r) = X.sec r
  rw [← hb, Ideal.quotientMap_mk]
  have h := DFunLike.congr_fun (crystallineFrameLift_residue X s hp 0) b
  change Ideal.Quotient.mk X.JB (crystallineFrameLift X s hp 0 b) =
    X.sec (PDCechNerve.augmentation p γ hp hJ s 0 b) at h
  exact h.trans (congrArg X.sec he)

variable {κ : Cardinal.{u}}

/-- 環の反対向きで読む、零次の分冪包の有限冪商の塔。 -/
def pdCechTowerZero (hsmall : Cardinal.mk (D).carrier ≤ κ) : ℕ ⥤ (CrysOver p γ R κ)ᵒᵖ :=
  crystallinePDQuotientSiteTower p γ R (D).dividedPowers
    (pdCechPrime_mem p γ hp R s 0) (D).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs 0)
    (pdCechResidueSection_base p γ hp R s hs 0) hsmall

/-- 全射な分冪枠の零次の塔は大きい結晶サイトで pro 弱終。 -/
theorem pdCechTowerZero_proWeaklyTerminal (hsmall : Cardinal.mk (D).carrier ≤ κ) :
    IsProWeaklyTerminal (pdCechTowerZero p γ hp R s hs hsmall) := by
  unfold pdCechTowerZero
  exact crystallinePDQuotientSiteTower_proWeaklyTerminal p γ R (D).dividedPowers
    (pdCechPrime_mem p γ hp R s 0) (D).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs 0)
    (pdCechResidueSection_base p γ hp R s hs 0) hsmall (fun X =>
      ⟨crystallineFrameLift X s hp 0, crystallineFrameLift_dp X s hp 0,
        crystallineFrameLift_comp_residueSection p γ hp R s hs X⟩)

/-- 小さい結晶サイトへ移した零次の塔。 -/
def pdCechSmallTowerZero (hsmall : Cardinal.mk (D).carrier ≤ κ) : ℕ ⥤ CrystallineSite p γ R κ :=
  pdCechTowerZero p γ hp R s hs hsmall ⋙ (equivSmallModel (CrysOver p γ R κ)).functor.op

/-- 小さい結晶サイトでも同じ塔が pro 弱終。 -/
theorem pdCechSmallTowerZero_proWeaklyTerminal (hsmall : Cardinal.mk (D).carrier ≤ κ) :
    IsProWeaklyTerminal (pdCechSmallTowerZero p γ hp R s hs hsmall) :=
  (pdCechTowerZero_proWeaklyTerminal p γ hp R s hs hsmall).map_equivalence
    (equivSmallModel (CrysOver p γ R κ)).op

end SerrePositivity.BhattScholze.Prismatic
