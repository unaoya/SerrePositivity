module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PadicIntMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism

/-!
# 結晶基底から Witt 基底への係数射

## 概要
既存の p 完備環への ℤ_p 作用を Witt 環に適用し、結晶 prism の間の射にする。

## 方針
ℤ_p 作用の一意性から Witt Frobenius との両立を得て、p 正則性で δ 両立に直す。
分冪との両立には既存の階乗消去の補題を使う。

## 規約
係数環は p 正則かつ p 進完備。prism の選択生成元は両側とも p。

## 使われ方
BS 著者版 Theorem 6.4 の小さい結晶の橋を Witt 係数へ底変換する。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

open SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable [hC : IsAdicComplete (Ideal.span {(p : C)}) C]

include hpC hC

private theorem wittModuleComplete :
    IsModuleComplete (WittVector p C) (p : WittVector p C)
      (ModuleCat.of (WittVector p C) (WittVector p C)) :=
  (wittCrystallinePrism hpC).complete_p

/-- 結晶基底から p 完備な Witt 環への標準の係数射。 -/
def crystallineWittBaseMap : crystallineBase.{u} p →+* WittVector p C :=
  (arcPadicIntMap p (WittVector p C) (wittModuleComplete p C hpC)).comp
    ULift.ringEquiv.toRingHom

private theorem map_frobenius_fixed (x : crystallineBase.{u} p) :
    WittVector.frobenius (crystallineWittBaseMap p C hpC x) =
      crystallineWittBaseMap p C hpC x := by
  let f := arcPadicIntMap p (WittVector p C) (wittModuleComplete p C hpC)
  have h := arcPadicIntMap_unique p (WittVector p C) (wittModuleComplete p C hpC)
    (WittVector.frobenius.comp f)
  exact RingHom.congr_fun h (ULift.ringEquiv x)

/-- 標準の係数射は二つの結晶 δ 構造と両立する。 -/
theorem crystallineWittBaseMap_isDeltaHom :
    (crystallineBasePrism.{u} p).deltaStructure.IsDeltaHom
      (wittCrystallinePrism hpC).deltaStructure (crystallineWittBaseMap p C hpC) := by
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ (witt_mul_prime_injective p C hpC)
  intro x
  change crystallineWittBaseMap p C hpC ((crystallineBaseDelta p).frobeniusLift x) =
    (wittCrystallineDelta hpC).frobeniusLift (crystallineWittBaseMap p C hpC x)
  rw [crystallineBaseDelta_frobenius, wittCrystallineDelta_frobenius, RingHom.id_apply]
  exact (map_frobenius_fixed p C hpC x).symm

/-- 選択生成元 p を保つ、結晶基底から Witt 結晶基底への prism 射。 -/
def crystallineWittBaseHom :
    OrientedPrism.Hom (crystallineBasePrism.{u} p) (wittCrystallinePrism hpC) where
  toRingHom := crystallineWittBaseMap p C hpC
  map_delta := crystallineWittBaseMap_isDeltaHom p C hpC
  ideal_le := by
    change Ideal.span {(crystallineBasePrism.{u} p).generator} ≤ _
    rw [Ideal.span_singleton_le_iff_mem, crystallineBase_generator]
    change crystallineWittBaseMap p C hpC (p : crystallineBase.{u} p) ∈
      Ideal.span {(p : WittVector p C)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _

/-- 結晶基底の (p) の分冪構造は、標準の係数射で Witt 基底の分冪構造に移る。 -/
theorem crystallineWittBaseMap_isDPMorphism
    (γ : DividedPowers (Ideal.span {(p : crystallineBase.{u} p)}))
    (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C)) :
    γ.IsDPMorphism (wittPdStructure p C hpC hlocalC) (crystallineWittBaseMap p C hpC) := by
  have hI : (Ideal.span {(p : crystallineBase.{u} p)}).map
      (crystallineWittBaseMap p C hpC) ≤ wittPdIdeal p C := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [Ideal.span_singleton_le_iff_mem]
    exact p_mem_wittPdIdeal p C
  apply isDPMorphism_of_ideal_le γ (wittPdStructure p C hpC hlocalC)
    (crystallineWittBaseMap p C hpC) hI (witt_mul_prime_injective p C hpC)
  intro m hm
  exact witt_isUnit_natCast p C m (hlocalC m hm)

end SerrePositivity.BhattScholze.Prismatic
