module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellWitnessSquare

/-!
概要：cell class 証人の全経路の射を、証人の端点証明を展開せず回収する。
方針：元の augmentation・経路・class 射の合成を明示する。
規約：射の定義に忠実な等式。使われ方：因子分解の同じ経路の正規化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  {f g : W ⟶ C} (v : DGAlgebra.Path.Witness R f g)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ algebra B N) (hκ : κ ≫ projection B N = p)

lemma cellClassWitness_hom : (cellClassWitness R p v hv N κ hκ).hom =
    DGAlgebra.cellAugmentation R W ≫ v.hom ≫ DGAlgebra.Path.map R κ := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero
