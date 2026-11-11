module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineZariskiIso
public import SerrePositivity.BhattScholze.Prismatic.CrystallineBaseStructureRestriction
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
import all SerrePositivity.BhattScholze.Prismatic.CrystallineBaseStructureRestriction
import all Mathlib.CategoryTheory.EssentiallySmall
import all Mathlib.CategoryTheory.Opposites

/-!
# 小さい結晶サイトの関手による主開被覆の保存

## 概要
剰余代数の引き戻しと分冪基底の制限は、小さい模型でも主開被覆を保つ。

## 方針
大きい厚化の圏での被覆保存を、小さい模型の単位自然同型で移す。

## 規約
被覆族の環の向きで述べる。サイトの矢印はその反転。

## 使われ方
Berthelot III.4、Stacks 07HN。結晶構造層の古典的な関手性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable {R R' : Type u} [CommRing R] [CommRing R']
variable [Algebra (k ⧸ J) R] [Algebra (k ⧸ J) R'] (κ : Cardinal.{u})

/-- 剰余代数の引き戻しによる小さいサイトの関手は主開被覆を保つ。 -/
theorem crysPullbackSite_isZariskiFamily (a : R →ₐ[k ⧸ J] R')
    {ι : Type u} [Finite ι] {X : CrysOverSmall p γ R' κ}
    (Y : ι → CrysOverSmall p γ R' κ) (f : ∀ i, X ⟶ Y i)
    (hf : IsCrystallineZariskiFamily p γ R' κ Y f) :
    let F := (crysPullbackSite p γ R κ a).unop
    IsCrystallineZariskiFamily p γ R κ (fun i => F.obj (Y i)) (fun i => F.map (f i)) := by
  let e := equivSmallModel (CrysOver p γ R κ)
  let F := (equivSmallModel (CrysOver p γ R' κ)).inverse ⋙ crysPullback p γ κ a
  apply (CrysOver.IsZariskiFamily.pullback a hf).of_iso
    (e.unitIso.app (F.obj X)) (fun i => e.unitIso.app (F.obj (Y i)))
  intro i
  exact e.unitIso.hom.naturality (F.map (f i))

variable {l : Type u} [CommRing l] {J' : Ideal l} (ε : DividedPowers J')
variable [Algebra (l ⧸ J') R]
variable (g : k →+* l) (hg : DividedPowers.IsDPMorphism γ ε g)
variable (hR : (algebraMap (l ⧸ J') R).comp ((Ideal.Quotient.mk J').comp g) =
  (algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J))

/-- 分冪基底の制限による小さいサイトの関手は主開被覆を保つ。 -/
theorem crysBaseRestrictionSite_isZariskiFamily
    {ι : Type u} [Finite ι] {X : CrysOverSmall p ε R κ}
    (Y : ι → CrysOverSmall p ε R κ) (f : ∀ i, X ⟶ Y i)
    (hf : IsCrystallineZariskiFamily p ε R κ Y f) :
    let F := (crysBaseRestrictionSite p γ ε R κ g hg hR).unop
    IsCrystallineZariskiFamily p γ R κ (fun i => F.obj (Y i)) (fun i => F.map (f i)) := by
  let e := equivSmallModel (CrysOver p γ R κ)
  let F := (equivSmallModel (CrysOver p ε R κ)).inverse ⋙
    crysBaseRestriction p γ ε R κ g hg hR
  apply (crysBaseRestriction_isZariskiFamily p γ ε R κ g hg hR hf).of_iso
    (e.unitIso.app (F.obj X)) (fun i => e.unitIso.app (F.obj (Y i)))
  intro i
  exact e.unitIso.hom.naturality (F.map (f i))

end SerrePositivity.BhattScholze.Prismatic
