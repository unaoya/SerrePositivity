module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 有限 p 冪商から結晶厚化への射

## 概要
分冪射が指定した p 冪を消せば、有限冪商からの厚化の射に降りる。

## 方針
商環の普遍性で代数射を作り、分冪射と剰余構造射の可換性を商写像で判定する。

## 規約
標的は実際の結晶厚化。消える p 冪を型に明示する。

## 使われ方
Berthelot III.4、Stacks 07HP。分冪包の塔の pro 弱終性と遷移射。
-/

public noncomputable section
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
variable (X : CrysOver p γ R κ) (e : ℕ) (f : D →ₐ[k] X.B)
variable (hf : DividedPowers.IsDPMorphism δ X.δ f.toRingHom)
variable (hkill : (p : X.B) ^ (e + 2) = 0)
variable (hcomm : (Ideal.quotientMap X.JB f.toRingHom
  (Ideal.map_le_iff_le_comap.mp hf.ideal_comp)).comp sec = X.sec)
local notation "P" => Ideal.span {(p : D)}

include hkill in
private theorem kill_mem (b : D) (hb : b ∈ (P ^ (e + 2))) : f b = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨a, rfl⟩ := hb
  rw [map_mul, map_pow, map_natCast, hkill, zero_mul]

/-- p 冪を消す代数射を有限冪商へ降ろす。 -/
def crystallinePDQuotientLiftAlg : D ⧸ (P ^ (e + 2)) →ₐ[k] X.B :=
  Ideal.Quotient.liftₐ _ f (kill_mem p γ R X e f hkill)

include hf in
/-- 降りた射は分冪を保つ。 -/
theorem crystallinePDQuotientLiftAlg_dp :
    DividedPowers.IsDPMorphism (PDAdicCompletion.quotientDividedPowers p δ hp e) X.δ
      (crystallinePDQuotientLiftAlg p γ R X e f hkill).toRingHom := by
  apply DividedPowers.IsDPMorphism.of_comp δ _ X.δ (Ideal.Quotient.mk (P ^ (e + 2)))
    (crystallinePDQuotientLiftAlg p γ R X e f hkill).toRingHom rfl
    (DividedPowers.Quotient.isDPMorphism _ _)
  exact hf

/-- 分冪と剰余を保つ射を有限 p 冪商からの厚化の射に降ろす。 -/
def crystallinePDQuotientLift :
    crystallinePDQuotient p γ R δ hp hbase sec hsec hsmall e ⟶ X := by
  let g := crystallinePDQuotientLiftAlg p γ R X e f hkill
  have hg := crystallinePDQuotientLiftAlg_dp p γ R δ hp X e f hf hkill
  let r := Ideal.quotientMap X.JB g.toRingHom
    (Ideal.map_le_iff_le_comap.mp hg.ideal_comp)
  have hr : r.comp (crystallineQuotientResidueMap p e) =
      Ideal.quotientMap X.JB f.toRingHom
        (Ideal.map_le_iff_le_comap.mp hf.ideal_comp) := by
    ext b
    rfl
  refine ⟨g, hg, ?_⟩
  intro a b hb
  have ha : r ((crystallineQuotientResidueMap p e) (sec a)) = X.sec a := by
    change (r.comp (crystallineQuotientResidueMap p e)) (sec a) = _
    rw [hr]
    exact DFunLike.congr_fun hcomm a
  exact (congrArg r hb).trans ha

end SerrePositivity.BhattScholze.Prismatic
