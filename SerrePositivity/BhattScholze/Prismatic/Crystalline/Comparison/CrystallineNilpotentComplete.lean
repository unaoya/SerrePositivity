module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-!
# 結晶厚化の p 進完備性

## 概要
p 冪零な結晶厚化は古典的に p 進完備である。

## 方針
p の主イデアルのある冪が零であることから、零イデアル進完備性を移す。

## 規約
p ねじれの正則性や Noether 性は仮定しない。

## 使われ方
Berthelot III.4、Stacks 07HP。完備分冪包の普遍性を結晶厚化へ適用する入力。
-/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Prismatic.CrysOver
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}

/-- p 冪零な厚化の台環は p 進完備。 -/
theorem isAdicComplete (X : CrysOver p γ R κ) :
    IsAdicComplete (Ideal.span {(p : X.B)}) X.B := by
  obtain ⟨N, hN⟩ := X.nilpotent
  apply SerrePositivity.isAdicComplete_of_pow_le (⊥ : Ideal X.B)
    (Ideal.span {(p : X.B)}) bot_le N _ X.B
  rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_zero]

end SerrePositivity.BhattScholze.Prismatic.CrysOver
