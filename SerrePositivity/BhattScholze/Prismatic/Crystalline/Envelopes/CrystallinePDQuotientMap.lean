module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotientLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotient
import all SerrePositivity.CommutativeAlgebra.DividedPowers.Envelopes.PDAdicCompletion

/-!
# 有限 p 冪商の分冪射についての関手性

## 概要
剰余構造射を保つ分冪射を、各有限冪商の結晶厚化の射へ降ろす。

## 方針
標的の商写像を合成し、有限冪商の持ち上げの普遍性を使う。

## 規約
源・標的の台環と濃度の上限、分冪と剰余の両立をすべて型に保持する。

## 使われ方
Berthelot III.4、Stacks 07HP。pd Čech の塔の単体構造射。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R]
variable {D E : Type u} [CommRing D] [CommRing E] [Algebra k D] [Algebra k E]
variable {I : Ideal D} {L : Ideal E} (δ : DividedPowers I) (ε : DividedPowers L)
variable (hpD : (p : D) ∈ I) (hpE : (p : E) ∈ L)
variable (baseD : DividedPowers.IsDPMorphism γ δ (algebraMap k D))
variable (baseE : DividedPowers.IsDPMorphism γ ε (algebraMap k E))
variable (secD : R →+* D ⧸ I) (secE : R →+* E ⧸ L)
variable (compD : secD.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
  (Ideal.Quotient.mk I).comp (algebraMap k D))
variable (compE : secE.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
  (Ideal.Quotient.mk L).comp (algebraMap k E))
variable {κ : Cardinal.{u}} (smallD : Cardinal.mk D ≤ κ) (smallE : Cardinal.mk E ≤ κ)
variable (f : D →ₐ[k] E) (hf : DividedPowers.IsDPMorphism δ ε f.toRingHom)
variable (hc : (Ideal.quotientMap L f.toRingHom
  (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)).comp secD = secE)
local notation "P" => Ideal.span {(p : D)}
local notation "T" => Ideal.span {(p : E)}
local notation "QD" e => crystallinePDQuotient p γ R δ hpD baseD secD compD smallD e
local notation "QE" e => crystallinePDQuotient p γ R ε hpE baseE secE compE smallE e

/-- 分冪射を同じ指数の有限 p 冪商へ降ろした厚化の射。 -/
def crystallinePDQuotientMap (e : ℕ) : (QD e) ⟶ (QE e) := by
  let q : E →ₐ[k] (QE e).B := Ideal.Quotient.mkₐ k (T ^ (e + 2))
  have hq : ε.IsDPMorphism (QE e).δ q.toRingHom := by
    change ε.IsDPMorphism (PDAdicCompletion.quotientDividedPowers p ε hpE e) _
    exact DividedPowers.Quotient.isDPMorphism _ _
  let g := q.comp f
  have hg : δ.IsDPMorphism (QE e).δ g.toRingHom := hq.comp _ hf
  have hz : (p : (QE e).B) ^ (e + 2) = 0 := by
    change (Ideal.Quotient.mk (T ^ (e + 2)) (p : E)) ^ (e + 2) = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : E)) _
  have hres : Ideal.quotientMap (QE e).JB g.toRingHom
      (Ideal.map_le_iff_le_comap.mp hg.ideal_comp) =
      (crystallineQuotientResidueMap p e).comp
        (Ideal.quotientMap L f.toRingHom (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)) := by
    ext b
    rfl
  have hsec : (Ideal.quotientMap (QE e).JB g.toRingHom
      (Ideal.map_le_iff_le_comap.mp hg.ideal_comp)).comp secD = (QE e).sec := by
    rw [hres, RingHom.comp_assoc, hc]
    rfl
  exact crystallinePDQuotientLift p γ R δ hpD baseD secD compD smallD (QE e) e g hg hz hsec

/-- 商の射は、源の代表元を元の分冪射で写した代表元へ送る。 -/
@[simp] theorem crystallinePDQuotientMap_mk (e : ℕ) (x : D) :
    (crystallinePDQuotientMap p γ R δ ε hpD hpE baseD baseE secD secE compD compE
      smallD smallE f hf hc e).toAlgHom (Ideal.Quotient.mk (P ^ (e + 2)) x) =
        Ideal.Quotient.mk (T ^ (e + 2)) (f x) := by
  dsimp only [crystallinePDQuotientMap, crystallinePDQuotientLift,
    crystallinePDQuotientLiftAlg]
  rfl

end SerrePositivity.BhattScholze.Prismatic
