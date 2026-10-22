module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientMap

/-!
概要：実平方零代数の係数移送が元の係数射影を保つ式を供給する。
方針：元の直和の対角射を射影へ合成する。
規約：元の双加群射を保持。使われ方：class の係数成分の照合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (A : Mon (Complex R)) {M N : Bimod A A} (f : M ⟶ N)

lemma coefficientMap_coefficient : (coefficientMap A f).hom ≫
    (biprod.snd : (algebra A N).X ⟶ N.X) =
      (biprod.snd : (algebra A M).X ⟶ M.X) ≫ f.hom :=
  biprod.map_snd _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
