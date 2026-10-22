module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellWitnessSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy

/-!
概要：全射準同型の上の二つの cell 比較経路が誘導する実 class 輸送を比較する。
方針：実 cell 充填を class 射で後合成し、相対模型の輸送経路へ持ち上げる。
規約：存在する class 二重経路を追加入力しない。使われ方：Postnikov の実三角形。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : W ⟶ C} (v w : DGAlgebra.Path.Witness R f g)
  (hv : v.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (hw : w.hom ≫ DGAlgebra.Path.map R p = (f ≫ p) ≫ DGAlgebra.Path.diagonal R B)
  (N : Bimod B B) (κ : C ⟶ SquareZero.algebra B N)
  (hκ : κ ≫ SquareZero.projection B N = p)

def cellTransportHomotopy : DGAlgebra.Path.Witness R
    (transport N (SquareZero.cellClassWitness R p v hv N κ hκ))
    (transport N (SquareZero.cellClassWitness R p w hw N κ hκ)) :=
  transportHomotopy N (SquareZero.cellClassWitnessSquare R p hs hq v w hv hw N κ hκ)

lemma cellTransportHomotopy_left : (cellTransportHomotopy R p hs hq v w hv hw N κ hκ).hom ≫
    DGAlgebra.Path.map R (relativeLeft N (cellAugmentation R W ≫ g ≫ κ)) =
      relativeLeft N (cellAugmentation R W ≫ f ≫ κ) ≫
        DGAlgebra.Path.diagonal R (cellResolution R W) := transportHomotopy_left N _

lemma cellTransportHomotopy_right : (cellTransportHomotopy R p hs hq v w hv hw N κ hκ).hom ≫
    DGAlgebra.Path.map R (relativeRight N (cellAugmentation R W ≫ g ≫ κ)) =
      relativeRight N (cellAugmentation R W ≫ f ≫ κ) ≫ DGAlgebra.Path.diagonal R B :=
  transportHomotopy_right N _

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
