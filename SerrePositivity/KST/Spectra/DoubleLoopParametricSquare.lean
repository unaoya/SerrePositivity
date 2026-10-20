module

public import SerrePositivity.KST.Spectra.DoubleLoopParametricAction
public import SerrePositivity.KST.Spectra.PointedParametricPostNaturality
public import SerrePositivity.KST.Spectra.TwoLoopSourceParametricPost
public import SerrePositivity.KST.Spectra.DeloopedTracedExchange

/-!
概要：元の随伴の全族 Ω 可換式を、標準の二重 loop 全族作用の厳密可換式へ移す。
方針：同じ全族可換式を標準 ihomAction の自然性で二度内部 Hom に移す。
規約：Kan 性や区間選択を使わない。使われ方：元の随伴への全族 trace の射影比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.LoopExchangePaths

/-- 元の厳密な全族 Ω 可換式は、同じ二重後合成と標準族作用の厳密な可換式となる。 -/
lemma doublePost_parametric_square {S P Y Y' Z Z' : PointedSimplicialSet.{u}}
    (a : Y ⟶ PointedObject.basedHom S Z) (a' : Y' ⟶ PointedObject.basedHom S Z')
    (v : P ⟶ PointedObject.basedHom Y Y') (w : P ⟶ PointedObject.basedHom Z Z')
    (hc : a ≫ PointedMapping.parametricPost S w =
      PointedMapping.transpose v ≫ PointedObject.basedHomMap P a') :
    doublePost a ≫ TwoLoopSource.standardParametricPost S w =
      doubleParametricPost v ≫ PointedObject.basedHomMap P (doublePost a') := by
  let K : PointedSimplicialSet.{u} := CirclePower.space.{u}
  have h₁ := PointedMapping.parametricPost_square K a a' v
    (w ≫ PointedMapping.ihomAction S Z Z') hc
  have h₂ := PointedMapping.parametricPost_square K
    (PointedObject.basedHomMap K a) (PointedObject.basedHomMap K a')
    (v ≫ PointedMapping.ihomAction K Y Y')
    ((w ≫ PointedMapping.ihomAction S Z Z') ≫ PointedMapping.ihomAction K
      (PointedObject.basedHom S Z) (PointedObject.basedHom S Z')) h₁
  exact h₂

end SerrePositivity.KST.Spectra.LoopExchangePaths
