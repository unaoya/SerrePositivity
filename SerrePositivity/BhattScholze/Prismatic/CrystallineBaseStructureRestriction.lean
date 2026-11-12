module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineBaseRestriction
public import SerrePositivity.BhattScholze.Prismatic.CrystallineSmallStructureSheaf
public import Mathlib.CategoryTheory.Whiskering
import all SerrePositivity.BhattScholze.Prismatic.CrystallineBaseRestriction
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.Category
import all Mathlib.CategoryTheory.Opposites
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.NatIso
import all Mathlib.CategoryTheory.EssentiallySmall
import all Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 分冪基底の制限と小さい結晶構造環

## 概要
分冪基底の射に沿う係数制限を小さいサイトへ移し、構造前層を比較する。

## 方針
台環を固定する制限関手と、小さい模型の同値の単位同型を使う。

## 規約
剰余代数の二つの係数構造の両立を型に残す。導来大域切断の関手性は扱わない。

## 使われ方
Berthelot III.4、BS 著者版 Theorem 6.4 の第0 Witt 成分による係数制限。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k l : Type u} [CommRing k] [CommRing l]
variable {J : Ideal k} {J' : Ideal l} (γ : DividedPowers J) (ε : DividedPowers J')
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R] [Algebra (l ⧸ J') R]
variable (κ : Cardinal.{u}) (g : k →+* l) (hg : DividedPowers.IsDPMorphism γ ε g)
variable (hR : (algebraMap (l ⧸ J') R).comp ((Ideal.Quotient.mk J').comp g) =
  (algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J))

/-- 分冪基底の射に沿う、小さい結晶サイトの制限関手。 -/
def crysBaseRestrictionSite : CrystallineSite p ε R κ ⥤ CrystallineSite p γ R κ :=
  ((equivSmallModel (CrysOver p ε R κ)).inverse ⋙ crysBaseRestriction p γ ε R κ g hg hR ⋙
    (equivSmallModel (CrysOver p γ R κ)).functor).op

/-- 基底制限による構造環の制限と、環値の係数制限との自然同型。 -/
def crystallineStructureRing_baseRestriction :
    (crysBaseRestrictionSite p γ ε R κ g hg hR).op ⋙ crystallineStructureRing p γ R κ ≅
      crystallineStructureRing p ε R κ ⋙ Under.map (CommRingCat.ofHom g) := by
  let eK := equivSmallModel (CrysOver p γ R κ)
  let eL := equivSmallModel (CrysOver p ε R κ)
  let F := crysBaseRestriction p γ ε R κ g hg hR
  refine NatIso.ofComponents (fun X =>
    (crysAlgebras p γ R κ).mapIso
      (eK.unitIso.app (F.obj (eL.inverse.obj X.unop.unop))).symm) ?_
  intro X Y h
  let a := F.map (eL.inverse.map h.unop.unop)
  have hc := congrArg (fun b => (crysAlgebras p γ R κ).map b)
    (eK.unitIso.inv.naturality a)
  change (crysAlgebras p γ R κ).map ((eK.functor ⋙ eK.inverse).map a) ≫
      (crysAlgebras p γ R κ).map (eK.unitIso.inv.app (F.obj (eL.inverse.obj Y.unop.unop))) =
    (crysAlgebras p γ R κ).map (eK.unitIso.inv.app (F.obj (eL.inverse.obj X.unop.unop))) ≫
      (crysAlgebras p γ R κ).map a
  simpa only [Functor.map_comp, Functor.id_map] using hc

end SerrePositivity.BhattScholze.Prismatic
