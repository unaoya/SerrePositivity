module

public import SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientMap
public import SerrePositivity.BhattScholze.Prismatic.PDCechResidueNaturality
import all SerrePositivity.BhattScholze.Prismatic.PDCechResidueNaturality
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve

/-!
# 結晶厚化の余単体的な有限冪商

## 概要
全射な枠の分冪 Čech 各項の有限 p 冪商を、厚化の圏の余単体的対象へ組む。

## 方針
各頂点写像の分冪射を商へ降ろし、代表元の公式と既存の関手則を使う。

## 規約
すべての項の濃度の上限を仮定する。各段は同じ p 冪で割る。

## 使われ方
Berthelot III.4、Stacks 07HP。pd Čech の塔の各段の Čech データ。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (hp : (p : k) ∈ J) (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable [Algebra k R] [IsScalarTower k (k ⧸ J) R]
variable {S : Type u} (s : S → R) (hs : Function.Surjective (pdFrameEval (k := k) s 0))
variable {κ : Cardinal.{u}} (hsmall : ∀ n, Cardinal.mk (PDCechNerve.term p γ hp
  (crysResidue_kernel_of_tower (J := J) R) s n).carrier ≤ κ)

/-- 頂点の写像を有限冪商の結晶厚化の射として読む。 -/
def pdCechQuotientMap (e : ℕ) {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1)) :
    ((pdCechQuotient p γ hp R s hs hsmall e m)) ⟶ ((pdCechQuotient p γ hp R s hs hsmall e n)) :=
  crystallinePDQuotientMap p γ R
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m).dividedPowers
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).dividedPowers
    (pdCechPrime_mem p γ hp R s m) (pdCechPrime_mem p γ hp R s n)
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m).isEnvelope.base_dp
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs m) (pdCechResidueSection p γ hp R s hs n)
    (pdCechResidueSection_base p γ hp R s hs m) (pdCechResidueSection_base p γ hp R s hs n)
    (hsmall m) (hsmall n) (PDCechNerve.mapCopies p γ hp (crysResidue_kernel_of_tower (J := J) R)
      s θ)
    (PDCechNerve.mapCopies_isDPMorphism p γ hp (crysResidue_kernel_of_tower (J := J) R) s θ)
    (pdCechResidueMap_section p γ hp R s hs θ) e

/-- 頂点写像の商の射は元の分冪射で代表元を写す。 -/
@[simp] theorem pdCechQuotientMap_mk (e : ℕ) {m n : ℕ}
    (θ : Fin (m + 1) → Fin (n + 1)) (x : (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower
      (J := J) R) s m).carrier) :
    (pdCechQuotientMap p γ hp R s hs hsmall e θ).toAlgHom
      (Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s m).carrier)}) ^ (e + 2)) x) =
        Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
          (crysResidue_kernel_of_tower (J := J) R) s n).carrier)}) ^ (e + 2))
          (PDCechNerve.mapCopies p γ hp (crysResidue_kernel_of_tower (J := J) R) s θ x) := by
  exact crystallinePDQuotientMap_mk p γ R
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m).dividedPowers
      (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).dividedPowers
    (pdCechPrime_mem p γ hp R s m) (pdCechPrime_mem p γ hp R s n)
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s m).isEnvelope.base_dp
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs m) (pdCechResidueSection p γ hp R s hs n)
    (pdCechResidueSection_base p γ hp R s hs m) (pdCechResidueSection_base p γ hp R s hs n)
    (hsmall m) (hsmall n) (PDCechNerve.mapCopies p γ hp (crysResidue_kernel_of_tower (J := J) R)
      s θ)
    (PDCechNerve.mapCopies_isDPMorphism p γ hp (crysResidue_kernel_of_tower (J := J) R) s θ)
    (pdCechResidueMap_section p γ hp R s hs θ) e x

/-- 有限冪商からの厚化の射は代表元上で判定できる。 -/
theorem pdCechQuotientHom_ext (e n : ℕ) {X : CrysOver p γ R κ}
    {f g : ((pdCechQuotient p γ hp R s hs hsmall e n)) ⟶ X} (h : ∀ x : (PDCechNerve.term p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s n).carrier,
      f.toAlgHom (Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s n).carrier)}) ^ (e + 2)) x) =
      g.toAlgHom (Ideal.Quotient.mk ((Ideal.span {(p : (PDCechNerve.term p γ hp
        (crysResidue_kernel_of_tower (J := J) R) s n).carrier)}) ^ (e + 2)) x)) : f = g := by
  apply CrysOver.Hom.ext p
  apply AlgHom.ext
  intro b
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact h x

/-- 各有限段の分冪 Čech 包を、結晶厚化の余単体的対象にする。 -/
def pdCechQuotientCosimplicial (e : ℕ) : CosimplicialObject (CrysOver p γ R κ) where
  obj n := (pdCechQuotient p γ hp R s hs hsmall e n.len)
  map θ := pdCechQuotientMap p γ hp R s hs hsmall e θ.toOrderHom
  map_id n := by
    apply pdCechQuotientHom_ext p γ hp R s hs hsmall e n.len
    intro x
    rw [pdCechQuotientMap_mk]
    change Ideal.Quotient.mk _ (PDCechNerve.mapCopies p γ hp (crysResidue_kernel_of_tower (J :=
      J) R) s id x) = _
    rw [PDCechNerve.mapCopies_id]
    rfl
  map_comp {a b c} θ φ := by
    apply pdCechQuotientHom_ext p γ hp R s hs hsmall e a.len
    intro x
    change (pdCechQuotientMap p γ hp R s hs hsmall e
      (fun i => φ.toOrderHom (θ.toOrderHom i))).toAlgHom (Ideal.Quotient.mk _ x) =
      (pdCechQuotientMap p γ hp R s hs hsmall e φ.toOrderHom).toAlgHom
        ((pdCechQuotientMap p γ hp R s hs hsmall e θ.toOrderHom).toAlgHom
          (Ideal.Quotient.mk _ x))
    rw [pdCechQuotientMap_mk, pdCechQuotientMap_mk, pdCechQuotientMap_mk,
      PDCechNerve.mapCopies_mapCopies]
    rfl

end SerrePositivity.BhattScholze.Prismatic
