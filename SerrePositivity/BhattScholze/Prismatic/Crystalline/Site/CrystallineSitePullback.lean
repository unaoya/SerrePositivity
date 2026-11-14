module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic

/-!
# 結晶厚化の剰余代数についての引き戻し

## 概要
剰余代数の射に沿い、同じ分冪厚化の剰余構造射を前合成する。

## 方針
環・イデアル・分冪・台環の射は固定し、構造射の可換性だけを確認する。

## 規約
環の向きでは剰余代数に反変。関手の恒等・合成と台環の保存は厳密な等式。

## 使われ方
Berthelot III.4、Stacks 07HM。big 結晶サイトの引き戻しと構造環の制限。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ)
variable {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
variable [Algebra (k ⧸ J) R] [Algebra (k ⧸ J) R'] [Algebra (k ⧸ J) R'']
variable (κ : Cardinal.{u})

/-- big 結晶厚化の剰余構造射を前合成する関手。 -/
def crysPullback (f : R →ₐ[k ⧸ J] R') :
    CrysOver p γ R' κ ⥤ CrysOver p γ R κ where
  obj X := {
    B := X.B
    JB := X.JB
    δ := X.δ
    base_dp := X.base_dp
    nilpotent := X.nilpotent
    sec := X.sec.comp f.toRingHom
    sec_comp := by
      ext a
      change X.sec (f (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a))) = _
      rw [f.commutes]
      exact DFunLike.congr_fun X.sec_comp a
    small := X.small }
  map g := ⟨g.toAlgHom, g.dp, fun r b h => g.comm_sec (f r) b h⟩
  map_id X := rfl
  map_comp g h := rfl

/-- 恒等射に沿う引き戻しは恒等関手。 -/
@[simp] theorem crysPullback_id :
    crysPullback p γ κ (AlgHom.id (k ⧸ J) R) = 𝟭 (CrysOver p γ R κ) := rfl

/-- 合成に沿う引き戻しは引き戻しの合成。 -/
theorem crysPullback_comp (f : R →ₐ[k ⧸ J] R') (g : R' →ₐ[k ⧸ J] R'') :
    crysPullback p γ κ (g.comp f) = crysPullback p γ κ g ⋙ crysPullback p γ κ f := rfl

/-- 引き戻しは基底の下の台環関手を厳密に保つ。 -/
@[simp] theorem crysPullback_crysAlgebras (f : R →ₐ[k ⧸ J] R') :
    crysPullback p γ κ f ⋙ crysAlgebras p γ R κ = crysAlgebras p γ R' κ := rfl

end SerrePositivity.BhattScholze.Prismatic
