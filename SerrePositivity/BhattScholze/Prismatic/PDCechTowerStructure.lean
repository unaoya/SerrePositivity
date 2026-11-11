module

public import SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
public import SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
public import Mathlib.CategoryTheory.Whiskering
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
import all Mathlib.CategoryTheory.EssentiallySmall
import all Mathlib.CategoryTheory.Opposites
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.Category
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.NatIso
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineTower
import all SerrePositivity.BhattScholze.Prismatic.PDCechCrystallineCosimplicial
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotient
import all SerrePositivity.BhattScholze.Prismatic.CrystallinePDQuotientTower
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# 分冪 Čech の塔上の構造環と標準射

## 概要
分冪 Čech 脈体から、有限冪商の結晶厚化上の構造環への射を余単体的に構成する。

## 方針
各項の商の標準射を使い、頂点写像との可換性は代表元の式で確認する。

## 規約
通常の環値の自然変換のみ。RΓ や Tot の辺は定義しない。

## 使われ方
Berthelot III.4、Stacks 07HP。結晶 Čech の塔と厳密な環模型の対応。
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

/-- 分冪 Čech 脈体から塔の有限段の構造環への標準自然変換。 -/
def pdCechQuotientStructureUnit (e : ℕ) :
    pdCechNerve p γ hp (crysResidue_kernel_of_tower (J := J) R) s ⟶
      pdCechQuotientCosimplicial p γ hp R s hs hsmall e ⋙ crysAlgebras p γ R κ where
  app n := Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk
    ((Ideal.span {(p : (PDCechNerve.term p γ hp
      (crysResidue_kernel_of_tower (J := J) R) s n.len).carrier)}) ^ (e + 2))))
  naturality m n θ := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact (pdCechQuotientMap_mk p γ hp R s hs hsmall e θ.toOrderHom x).symm

/-- 標準自然変換は塔の隣り合う遷移と両立する。 -/
theorem pdCechQuotientStructureUnit_transition (e : ℕ) :
    pdCechQuotientStructureUnit p γ hp R s hs hsmall (e + 1) ≫
      Functor.whiskerRight (pdCechQuotientTransition p γ hp R s hs hsmall e)
        (crysAlgebras p γ R κ) =
    pdCechQuotientStructureUnit p γ hp R s hs hsmall e := by
  apply NatTrans.ext
  funext n
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact crystallinePDQuotientTransition_mk p γ R
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).dividedPowers
    (pdCechPrime_mem p γ hp R s n.len)
    (PDCechNerve.term p γ hp (crysResidue_kernel_of_tower (J := J) R) s n.len).isEnvelope.base_dp
    (pdCechResidueSection p γ hp R s hs n.len)
    (pdCechResidueSection_base p γ hp R s hs n.len) (hsmall n.len)
    e (e + 1) (Nat.le_succ e) x

/-- 小さい結晶サイトの構造前層を各有限 Čech 段に制限すると、その段の台環を得る。 -/
def pdCechQuotientSmallStructureIso (e : ℕ) :
    (pdCechQuotientCosimplicial p γ hp R s hs hsmall e ⋙
      (equivSmallModel (CrysOver p γ R κ)).functor).op.op ⋙
        crystallineStructureRing p γ R κ ≅
    unopUnop _ ⋙ pdCechQuotientCosimplicial p γ hp R s hs hsmall e ⋙
      crysAlgebras p γ R κ := by
  let E := equivSmallModel (CrysOver p γ R κ)
  let N := pdCechQuotientCosimplicial p γ hp R s hs hsmall e
  refine NatIso.ofComponents (fun X =>
    (crysAlgebras p γ R κ).mapIso (E.unitIso.app (N.obj X.unop.unop)).symm) ?_
  intro X Y h
  have hc := congrArg (fun a => (crysAlgebras p γ R κ).map a)
    (E.unitIso.inv.naturality (N.map h.unop.unop))
  change (crysAlgebras p γ R κ).map ((E.functor ⋙ E.inverse).map (N.map h.unop.unop)) ≫
      (crysAlgebras p γ R κ).map (E.unitIso.inv.app (N.obj Y.unop.unop)) =
    (crysAlgebras p γ R κ).map (E.unitIso.inv.app (N.obj X.unop.unop)) ≫
      (crysAlgebras p γ R κ).map (N.map h.unop.unop)
  simpa only [Functor.map_comp, Functor.id_map] using hc

end SerrePositivity.BhattScholze.Prismatic
