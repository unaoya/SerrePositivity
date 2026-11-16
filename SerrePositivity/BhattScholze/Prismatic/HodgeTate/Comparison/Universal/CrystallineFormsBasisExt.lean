module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.AffineOrientedRawBasis
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Universal.QuotientBasisExt
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineAffineFormsUnit

/-!
# 元の結晶的な完備形式の基底による射の判定

## 概要
生成元がpのとき、元の通常形式の基底の完備化単位で基底環線形射を判定する。

## 方針
元の完備化単位の同型を通して、剰余係数基底による外延性を使う。

## 規約
終域に剰余係数作用を要求しない。

## 使われ方
HT04.R2の零次・一次の元の正方形を基底上の値から戻す。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
open CategoryTheory SerrePositivity.DeRham HTUniversalCrystallineInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- 完備形式と二つの係数作用を照合する外延性の検査に必要。
set_option maxHeartbeats 600000
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]

/-- 元の基底環線形射は、元の形式基底の完備化単位で決まる。 -/
theorem crystallineForms_basis_ext (Q : OrientedPrism p B) (hg : Q.generator = (p : B))
    (r i : ℕ) (N : ModuleCat.{u} B) :
    letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
    ∀ g h : affineForms Q r i →ₗ[B] N,
      (∀ v, g (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p i
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v)) =
        h (completedFormsUnit (B ⧸ Q.ideal) (formVars.{u} r) p i
        (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i v))) → g = h := by
  letI := Module.compHom (affineForms Q r i) (affineBaseToPolynomialMap Q r)
  letI := Module.compHom (forms (B ⧸ Q.ideal) (formVars.{u} r) i) (Ideal.Quotient.mk Q.ideal)
  intro g h hb
  let e := crystallineAffineBaseFormsUnitIso Q r hg i
  have he : g.comp e.toLinearMap = h.comp e.toLinearMap := by
    apply quotientBasis_linearMap_ext Q.ideal (polynomialFormsBasis (B ⧸ Q.ideal) (formVars.{u} r) i)
    intro v
    simpa only [e, LinearMap.comp_apply, LinearEquiv.coe_coe,
      crystallineAffineBaseFormsUnitIso_apply] using hb v
  apply LinearMap.ext
  intro x
  obtain ⟨w, rfl⟩ := e.surjective x
  exact LinearMap.congr_fun he w

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
