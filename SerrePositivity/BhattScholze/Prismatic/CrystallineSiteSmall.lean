module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineTransport
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Logic.Equiv.Set

/-!
# 濃度を固定した結晶厚化の小さい模型

## 概要
濃度 ≤ κ の厚化の圏が元の宇宙で本質的に小さいことを示す。

## 方針
κ の代表型の部分集合に環・代数・分冪の構造を載せた型を使う。
任意の厚化を単射の像へ移し、誘導圏からの充満忠実かつ本質的全射な関手を得る。

## 規約
濃度による本質的小ささ自体に cutoff の下限は必要ない。

## 使われ方
Berthelot III.4、Stacks 07HM。小さい affine 結晶サイトとその構造前層。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R] (κ : Cardinal.{u})

namespace CrysOver
/-- 固定した型の部分集合を台に持つ結晶厚化の構造。 -/
structure CarrierModel where
  support : Set κ.out
  [ring : CommRing support]
  [alg : Algebra k support]
  ideal : Ideal support
  dividedPowers : DividedPowers ideal
  base_dp : DividedPowers.IsDPMorphism γ dividedPowers (algebraMap k support)
  nilpotent : IsNilpotent (p : support)
  sec : R →+* support ⧸ ideal
  sec_comp : sec.comp ((algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J)) =
    (Ideal.Quotient.mk ideal).comp (algebraMap k support)

attribute [instance] CarrierModel.ring CarrierModel.alg

/-- 固定された台を持つ厚化を、元の厚化の圏へ戻す。 -/
def CarrierModel.toOver (X : CarrierModel p γ R κ) : CrysOver p γ R κ where
  B := X.support
  JB := X.ideal
  δ := X.dividedPowers
  base_dp := X.base_dp
  nilpotent := X.nilpotent
  sec := X.sec
  sec_comp := X.sec_comp
  small := (Cardinal.mk_subtype_le _).trans (Cardinal.mk_out κ).le

/-- 固定された台を持つ厚化の型に、元の圏から射を誘導する。 -/
abbrev CarrierCategory := InducedCategory (CrysOver p γ R κ) (CarrierModel.toOver p γ R κ)

/-- 固定された台を忘れる充満忠実な関手。 -/
abbrev carrierFunctor : CarrierCategory p γ R κ ⥤ CrysOver p γ R κ :=
  inducedFunctor (CarrierModel.toOver p γ R κ)

instance : (carrierFunctor p γ R κ).EssSurj where
  mem_essImage X := by
    have h : Cardinal.mk X.B ≤ Cardinal.mk κ.out := by
      simpa only [Cardinal.mk_out] using X.small
    obtain ⟨i⟩ := (Cardinal.le_def X.B κ.out).mp h
    let e0 : Set.range i ≃ X.B := (Equiv.ofInjective i i.injective).symm
    let : CommRing (Set.range i) := e0.commRing
    let : Algebra k (Set.range i) := e0.algebra k
    let e : X.B ≃ₐ[k] Set.range i := (e0.algEquiv k).symm
    have hs : Cardinal.mk (Set.range i) ≤ κ :=
      (Cardinal.mk_subtype_le _).trans (Cardinal.mk_out κ).le
    let Y := X.transport e hs
    let Z : CarrierModel p γ R κ := {
      support := Set.range i
      ring := Y.ring
      alg := Y.alg
      ideal := Y.JB
      dividedPowers := Y.δ
      base_dp := Y.base_dp
      nilpotent := Y.nilpotent
      sec := Y.sec
      sec_comp := Y.sec_comp }
    exact ⟨Z, ⟨(X.transportIso e hs).symm⟩⟩

/-- 濃度 ≤ κ の結晶厚化の圏は元の宇宙で本質的に小さい。 -/
theorem essentiallySmall : EssentiallySmall.{u} (CrysOver p γ R κ) := by
  let : (carrierFunctor p γ R κ).IsEquivalence := {}
  exact EssentiallySmall.mk' (carrierFunctor p γ R κ).asEquivalence.symm

end CrysOver

instance : EssentiallySmall.{u} (CrysOver p γ R κ) :=
  CrysOver.essentiallySmall p γ R κ

/-- 結晶厚化の小さい模型、環の向き。 -/
abbrev CrysOverSmall : Type u := SmallModel (CrysOver p γ R κ)

/-- affine 結晶サイトの小さい圏。 -/
abbrev CrystallineSite : Type u := (CrysOverSmall p γ R κ)ᵒᵖ

end SerrePositivity.BhattScholze.Prismatic
