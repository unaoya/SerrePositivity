module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineResidue
public import Mathlib.Algebra.Algebra.TransferInstance
import all Mathlib.Algebra.Algebra.Equiv
import all Mathlib.Algebra.Ring.Equiv
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 結晶厚化の代数同型による移送

## 概要
台環の代数同型に沿って分冪イデアル・剰余構造射を移す。

## 方針
分冪は既存の環同型による移送、剰余は商環の同型を使う。

## 規約
濃度の上限は移送先について明示する。

## 使われ方
Berthelot III.4、Stacks 07HM。濃度を固定した小さい結晶サイトの構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
namespace CrysOver
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}
variable (X : CrysOver p γ R κ) {D : Type u} [CommRing D] [Algebra k D]
variable (e : X.B ≃ₐ[k] D) (hD : Cardinal.mk D ≤ κ)

/-- 代数同型に沿う分冪厚化の移送。 -/
def transport : CrysOver p γ R κ where
  B := D
  JB := X.JB.map e.toRingHom
  δ := X.δ.ofRingEquiv (e := e.toRingEquiv) rfl
  base_dp := by
    have he : X.δ.IsDPMorphism (X.δ.ofRingEquiv (e := e.toRingEquiv) rfl) e.toRingHom :=
      ⟨le_rfl, fun x hx => by simp⟩
    have hc : e.toRingHom.comp (algebraMap k X.B) = algebraMap k D :=
      RingHom.ext e.commutes
    rw [← hc]
    exact he.comp _ X.base_dp
  nilpotent := by
    simpa only [map_natCast] using X.nilpotent.map e.toRingHom
  sec := (Ideal.quotientEquiv X.JB (X.JB.map e.toRingHom) e.toRingEquiv rfl).toRingHom.comp X.sec
  sec_comp := by
    ext a
    change (Ideal.quotientEquiv X.JB _ e.toRingEquiv rfl)
      (X.sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a))) = _
    rw [show X.sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a)) =
      Ideal.Quotient.mk X.JB (algebraMap k X.B a) from DFunLike.congr_fun X.sec_comp a]
    change Ideal.Quotient.mk _ (e (algebraMap k X.B a)) = _
    rw [e.commutes]
    rfl
  small := hD

/-- 移送先への標準の分冪厚化の射。 -/
def transportHom : X ⟶ X.transport e hD where
  toAlgHom := e.toAlgHom
  dp := by
    refine ⟨le_rfl, ?_⟩
    intro n x hx
    change e (X.δ.dpow n (e.symm (e x))) = e (X.δ.dpow n x)
    rw [e.symm_apply_apply]
  comm_sec r b h := by
    change Ideal.Quotient.mk _ (e b) = (Ideal.quotientEquiv X.JB _ e.toRingEquiv rfl) (X.sec r)
    rw [← h]
    rfl

/-- 移送元への逆向きの標準射。 -/
def transportInv : X.transport e hD ⟶ X where
  toAlgHom := e.symm.toAlgHom
  dp := by
    refine ⟨?_, ?_⟩
    · change (X.JB.map e.toRingHom).map e.symm.toRingHom ≤ X.JB
      rw [Ideal.map_map]
      have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id X.B :=
        RingHom.ext e.symm_apply_apply
      rw [he, Ideal.map_id]
    · intro n x hx
      change X.δ.dpow n (e.symm x) =
        e.symm ((X.δ.ofRingEquiv (e := e.toRingEquiv) rfl).dpow n x)
      exact (e.symm_apply_apply _).symm
  comm_sec r b h := by
    change Ideal.Quotient.mk X.JB (e.symm b) = X.sec r
    apply (Ideal.quotientEquiv X.JB _ e.toRingEquiv rfl).injective
    change Ideal.Quotient.mk _ (e (e.symm b)) = _
    change Ideal.Quotient.mk (X.JB.map e.toRingHom) b =
      (Ideal.quotientEquiv X.JB _ e.toRingEquiv rfl) (X.sec r) at h
    rw [e.apply_symm_apply]
    exact h

/-- 台環の代数同型は結晶厚化の同型を与える。 -/
def transportIso : X ≅ X.transport e hD where
  hom := X.transportHom e hD
  inv := X.transportInv e hD
  hom_inv_id := by
    apply Hom.ext p
    ext b
    change e.symm (e b) = b
    exact e.symm_apply_apply b
  inv_hom_id := by
    apply Hom.ext p
    ext b
    change e (e.symm b) = b
    exact e.apply_symm_apply b

end CrysOver
end SerrePositivity.BhattScholze.Prismatic
