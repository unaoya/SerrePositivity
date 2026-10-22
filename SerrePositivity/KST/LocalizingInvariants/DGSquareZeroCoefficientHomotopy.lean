module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientFormula
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathHomotopy

/-!
概要：平方零代数の係数像を結ぶ実経路から、元の係数射の鎖ホモトピーを回収する。
方針：元の乗法的経路の鎖ホモトピーに係数射影を後合成する。
規約：像の経路から元の経路の存在は推測しない。使われ方：class の係数障害。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable (R : Type u) [CommRing R] {A W : Mon (Complex R)} {M N : Bimod A A}
  (m : M ⟶ N) (s t : W ⟶ algebra A M)

/-- 実 class 像の経路が与える、指定した元の係数射の鎖ホモトピー。 -/
def coefficientHomotopy (w : DGAlgebra.Path.Witness R
    (s ≫ coefficientMap A m) (t ≫ coefficientMap A m)) :
    Homotopy ((s.hom ≫ (biprod.snd : (algebra A M).X ⟶ M.X)) ≫ m.hom)
      ((t.hom ≫ (biprod.snd : (algebra A M).X ⟶ M.X)) ≫ m.hom) := by
  let π : (algebra A N).X ⟶ N.X := biprod.snd
  have h := w.chainHomotopy.compRight π
  have hs : (s ≫ coefficientMap A m).hom ≫ π =
      (s.hom ≫ (biprod.snd : (algebra A M).X ⟶ M.X)) ≫ m.hom := by
    change (s.hom ≫ (coefficientMap A m).hom) ≫ biprod.snd = _
    rw [Category.assoc, coefficientMap_coefficient, ← Category.assoc]
  have ht : (t ≫ coefficientMap A m).hom ≫ π =
      (t.hom ≫ (biprod.snd : (algebra A M).X ⟶ M.X)) ≫ m.hom := by
    change (t.hom ≫ (coefficientMap A m).hom) ≫ biprod.snd = _
    rw [Category.assoc, coefficientMap_coefficient, ← Category.assoc]
  rw [hs, ht] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.SquareZero
