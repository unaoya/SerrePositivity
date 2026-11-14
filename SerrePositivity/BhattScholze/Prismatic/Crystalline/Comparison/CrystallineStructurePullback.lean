module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSmallSiteTopology
public import Mathlib.CategoryTheory.Whiskering
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSmallSiteTopology
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSitePullback
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.Category
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.NatIso
import all Mathlib.CategoryTheory.Opposites
import all Mathlib.CategoryTheory.EssentiallySmall

/-!
# 小さい結晶サイトの引き戻しと構造環

## 概要
剰余代数の射に沿うサイトの圏の関手で構造前層を制限すると、元の構造前層になる。

## 方針
大きい厚化の圏では台環の保存は厳密。小さい模型では同値の単位同型で比較する。

## 規約
通常の基底環の下の環値の自然同型。層コホモロジーの辺には組み立てない。

## 使われ方
Berthelot III.4、Stacks 07HM。結晶構造環の古典的な関手性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable {R R' : Type u} [CommRing R] [CommRing R']
variable [Algebra (k ⧸ J) R] [Algebra (k ⧸ J) R'] (κ : Cardinal.{u})

/-- 小さいサイトの引き戻しによる構造環の制限の標準自然同型。 -/
def crystallineStructureRing_pullback (f : R →ₐ[k ⧸ J] R') :
    (crysPullbackSite p γ R κ f).op ⋙ crystallineStructureRing p γ R κ ≅
      crystallineStructureRing p γ R' κ := by
  let eR := equivSmallModel (CrysOver p γ R κ)
  let eR' := equivSmallModel (CrysOver p γ R' κ)
  refine NatIso.ofComponents (fun X =>
    (crysAlgebras p γ R κ).mapIso
      (eR.unitIso.app ((crysPullback p γ κ f).obj (eR'.inverse.obj X.unop.unop))).symm) ?_
  intro X Y g
  let h := (crysPullback p γ κ f).map (eR'.inverse.map g.unop.unop)
  have hc := congrArg (fun a => (crysAlgebras p γ R κ).map a)
    (eR.unitIso.inv.naturality h)
  change (crysAlgebras p γ R κ).map ((eR.functor ⋙ eR.inverse).map h) ≫
      (crysAlgebras p γ R κ).map
        (eR.unitIso.inv.app ((crysPullback p γ κ f).obj (eR'.inverse.obj Y.unop.unop))) =
    (crysAlgebras p γ R κ).map
      (eR.unitIso.inv.app ((crysPullback p γ κ f).obj (eR'.inverse.obj X.unop.unop))) ≫
        (crysAlgebras p γ R κ).map h
  simpa only [Functor.map_comp, Functor.id_map] using hc

end SerrePositivity.BhattScholze.Prismatic
