module

public import SerrePositivity.BhattScholze.Prismatic.WittCrystallinePrism
public import SerrePositivity.BhattScholze.Prismatic.BigPDModel
public import SerrePositivity.BhattScholze.Prism.Basic.UniversalOriented
import all SerrePositivity.BhattScholze.Prismatic.PDSmallRawEnvelope

/-!
# 普遍向き付き prism の Witt 係数比較

## 概要
普遍向き付き prism の剰余環から得る Witt 結晶 prism とその係数射を定める。

## 方針
K2 の正則性を使い、剰余の導来 p 完備性を古典的 p 完備性へ移す。
一般の Witt 係数比較をその入力に適用する。

## 規約
普遍向き付き prism は生成元を選んだ K2 の模型。

## 使われ方
BS 著者版 Theorem 6.4 の普遍基底と大きい分冪 Čech 模型。
-/

public noncomputable section

universe u

open CategoryTheory SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime]

/-- 普遍向き付き prism の剰余環。 -/
abbrev UniversalOrientedResidue :=
  UniversalOrientedPrismRing.{u} p ⧸ (universalOrientedPrism p).ideal

/-- K2 の普遍基底の剰余は古典的に p 進完備。 -/
theorem universalOrientedResidue_complete :
    IsAdicComplete (Ideal.span {(p : UniversalOrientedResidue.{u} p)})
      (UniversalOrientedResidue.{u} p) := by
  apply (isRingModuleComplete_iff_isAdicComplete_natCast (UniversalOrientedResidue.{u} p) p
    (universalOrientedPrism_mod_generator_p_regular p)).mp
  exact isModuleComplete_principal_quotient_natCast (UniversalOrientedPrismRing p) p
    (universalOrientedPrism p).generator (universalOrientedPrism p).complete_p

/-- 普遍向き付き prism の剰余上の Witt 結晶 prism。 -/
def universalWittCrystallinePrism :
    OrientedPrism p (WittVector p (UniversalOrientedResidue.{u} p)) :=
  letI := universalOrientedResidue_complete.{u} p
  wittCrystallinePrism (universalOrientedPrism_mod_generator_p_regular p)

/-- 普遍向き付き prism から Witt 結晶 prism への係数射。 -/
def universalWittPrismMap :
    OrientedPrism.Hom (universalOrientedPrism.{u} p) (universalWittCrystallinePrism p) :=
  letI := universalOrientedResidue_complete.{u} p
  psiPrism (universalOrientedPrism p) (universalOrientedPrism_regular p).1
    (universalOrientedPrism_mod_generator_p_regular p)

/-- 普遍剰余環上の多項式代数を Witt 基底上の大きい分冪模型へ送る。 -/
def universalWittBigPDModel :
    Poly (UniversalOrientedResidue.{u} p) ⥤ SimplexCategory ⥤
      Under (CommRingCat.of (WittVector p (UniversalOrientedResidue.{u} p))) :=
  wittBigPdModel (universalOrientedPrism p) (universalOrientedPrism_mod_generator_p_regular p)
    (PDSmallRawEnvelope.isUnit_natCast_of_not_dvd p (universalOrientedResidue_complete p))

end SerrePositivity.BhattScholze.Prismatic
