module

public import SerrePositivity.BhattScholze.Prismatic.PDCechTowerStructure
import all SerrePositivity.BhattScholze.Prismatic.PDCechTowerStructure
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientMap
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 枠の射を有限 Čech 段の結晶サイトの射へ降ろす

## 概要
表示を替える分冪枠の射を、各有限 p 冪商の結晶厚化の射として読む。

## 方針
増強の自然性で剰余構造射を照合し、商の普遍性で射を降ろす。

## 規約
同じ分冪基底・同じ剰余代数の二つの全射な枠を扱う。

## 使われ方
Berthelot III.4、Stacks 07HP。厳密な枠の比較と結晶サイトの辺との照合。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S S' : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable (s' : S' → R) (hs' : Function.Surjective (pdFrameEval (k := k) s' 0))
variable {κ : Cardinal.{u}} (hsmall : ∀ n, Cardinal.mk (PDCechNerve.term p γ hp
  (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ)
variable (hsmall' : ∀ n, Cardinal.mk (PDCechNerve.term p γ hp
  (crysResidue_kernel_of_tower (J := J) R) s' n).carrier ≤ κ)
variable (φ : S → (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s' 0).carrier)
variable (hφ : ∀ t, PDCechNerve.augmentation p γ hp
  (crysResidue_kernel_of_tower (J := J) R) s' 0 (φ t) = s t)

include hs hs' in
private theorem frame_section (n : ℕ) :
    (Ideal.quotientMap _ (PDCechNerve.mapAt p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n).toRingHom
      (Ideal.map_le_iff_le_comap.mp (PDCechNerve.mapAt_isDPMorphism p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n).ideal_comp)).comp
      (pdCechResidueSection p γ hp R s hs n) =
        pdCechResidueSection p γ hp R s' hs' n := by
  let E := crystallineCechResidueEquiv p γ hp (crysResidue_kernel_of_tower (J := J) R) s hs n
  let E' := crystallineCechResidueEquiv p γ hp (crysResidue_kernel_of_tower (J := J) R) s' hs' n
  let f := Ideal.quotientMap _ (PDCechNerve.mapAt p γ hp
    (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n).toRingHom
    (Ideal.map_le_iff_le_comap.mp (PDCechNerve.mapAt_isDPMorphism p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n).ideal_comp)
  have hf : E'.toRingHom.comp f = E.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro x
    change E' (Ideal.Quotient.mk _ (PDCechNerve.mapAt p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n x)) = E (Ideal.Quotient.mk _ x)
    rw [crystallineCechResidueEquiv_mk, crystallineCechResidueEquiv_mk,
      PDCechNerve.augmentation_mapAt]
  ext r
  apply E'.injective
  change E' (f (E.symm r)) = E' (E'.symm r)
  exact (DFunLike.congr_fun hf (E.symm r)).trans (E.apply_symm_apply r) |>.trans
    (E'.apply_symm_apply r).symm

/-- 枠の射を各有限 p 冪商の実際の結晶厚化の射へ降ろす。 -/
def pdCechFrameQuotientAt (e n : ℕ) :
    pdCechQuotient p γ hp R s hs hsmall e n ⟶
      pdCechQuotient p γ hp R s' hs' hsmall' e n :=
  crystallinePDQuotientMap p γ R
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).dividedPowers
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s' n).dividedPowers
    (pdCechPrime_mem p γ hp R s n) (pdCechPrime_mem p γ hp R s' n)
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).isEnvelope.base_dp
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s' n).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs n) (pdCechResidueSection p γ hp R s' hs' n)
    (pdCechResidueSection_base p γ hp R s hs n) (pdCechResidueSection_base p γ hp R s' hs' n)
    (hsmall n) (hsmall' n)
    (PDCechNerve.mapAt p γ hp (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n)
    (PDCechNerve.mapAt_isDPMorphism p γ hp (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n)
    (frame_section p γ hp R s hs s' hs' φ hφ n) e

/-- 商へ降ろした枠の射の、任意の代表元上の公式。 -/
theorem pdCechFrameQuotientAt_mk (e n : ℕ)
    (x : (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).carrier) :
    (pdCechFrameQuotientAt p γ hp R s hs s' hs' hsmall hsmall' φ hφ e n).toAlgHom
      (Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s n).carrier)}) ^ (e + 2)) x) =
      Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s' n).carrier)}) ^ (e + 2))
        (PDCechNerve.mapAt p γ hp (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ n x) := by
  unfold pdCechFrameQuotientAt
  exact crystallinePDQuotientMap_mk ..

/-- 枠の射は有限段でも余単体的な結晶厚化の自然変換となる。 -/
def pdCechFrameQuotientMap (e : ℕ) :
    pdCechQuotientCosimplicial p γ hp R s hs hsmall e ⟶
      pdCechQuotientCosimplicial p γ hp R s' hs' hsmall' e where
  app n := pdCechFrameQuotientAt p γ hp R s hs s' hs' hsmall hsmall' φ hφ e n.len
  naturality m n θ := by
    apply pdCechQuotientHom_ext p γ hp R s hs hsmall e m.len
    intro x
    change (pdCechFrameQuotientAt p γ hp R s hs s' hs' hsmall hsmall' φ hφ e n.len).toAlgHom
      ((pdCechQuotientMap p γ hp R s hs hsmall e θ.toOrderHom).toAlgHom (Ideal.Quotient.mk _ x)) =
      (pdCechQuotientMap p γ hp R s' hs' hsmall' e θ.toOrderHom).toAlgHom
        ((pdCechFrameQuotientAt p γ hp R s hs s' hs' hsmall hsmall' φ hφ e m.len).toAlgHom
          (Ideal.Quotient.mk _ x))
    rw [pdCechQuotientMap_mk, pdCechFrameQuotientAt_mk,
      pdCechFrameQuotientAt_mk, pdCechQuotientMap_mk]
    exact congrArg (Ideal.Quotient.mk _)
      (DFunLike.congr_fun (PDCechNerve.mapAt_naturality p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ θ.toOrderHom) x)

/-- 枠の厳密な比較と、サイトの構造環への標準射との可換正方形。 -/
theorem pdCechFrameQuotientMap_structure (e : ℕ) :
    pdCechNerveMap p γ hp (crysResidue_kernel_of_tower (J := J) R) s s' φ hφ ≫
        pdCechQuotientStructureUnit p γ hp R s' hs' hsmall' e =
      pdCechQuotientStructureUnit p γ hp R s hs hsmall e ≫
        Functor.whiskerRight
          (pdCechFrameQuotientMap p γ hp R s hs s' hs' hsmall hsmall' φ hφ e)
          (crysAlgebras p γ R κ) := by
  apply NatTrans.ext
  funext n
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (pdCechFrameQuotientAt_mk p γ hp R s hs s' hs' hsmall hsmall' φ hφ e n.len x).symm

end SerrePositivity.BhattScholze.Prismatic
