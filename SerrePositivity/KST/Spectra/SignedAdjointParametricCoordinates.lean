module

public import SerrePositivity.KST.Spectra.SignedAdjointNaturalityCoordinates
public import SerrePositivity.KST.Spectra.DoubleLoopParametricSquare

/-!
概要：通常円と Kan 円の混合二重 loop の標準全族作用と射影の厳密自然性。
方針：同じ内側 ihomAction に対して、外側の円の源制限の全族可換式を使う。
規約：区間や Kan 性不要。使われ方：符号付き随伴の実区間の全族移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.SignedAdjointPaths
open LoopExchangePaths

/-- 同じ混合二重 loop に標準 ihomAction を二度作用させる全族射。 -/
def targetParametricPost {P Z Z' : PointedSimplicialSet.{u}}
    (v : P ⟶ PointedObject.basedHom Z Z') : target Z ⟶ PointedObject.basedHom P (target Z') :=
  PointedMapping.parametricPost PointedSimplicialSet.circle.{u}
    (v ≫ PointedMapping.ihomAction CirclePower.space.{u} Z Z')

/-- 外側の通常円への射影は、同じ標準全族作用と厳密に可換。 -/
lemma projection_parametric {P Z Z' : PointedSimplicialSet.{u}}
    (v : P ⟶ PointedObject.basedHom Z Z') :
    projection Z ≫ targetParametricPost v =
      doubleParametricPost v ≫ PointedObject.basedHomMap P (projection Z') :=
  (PointedMapping.parametricPost_restrict CirclePower.unit.{u}
    (v ≫ PointedMapping.ihomAction CirclePower.space.{u} Z Z')).symm

end SerrePositivity.KST.Spectra.SignedAdjointPaths
