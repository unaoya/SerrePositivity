module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellOverClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy

/-!
概要：元の Postnikov 自然性経路の class 比較を、共通底上の実輸送比較へ移す。
方針：元の摂動射上で cell 二重充填し、同じ P に底変更して実模型へ持ち上げる。
規約：元の自然性経路を一方の経路に使う。使われ方：Γ の自然性比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C)
  (w : Path.Witness R
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverSource R B C P n hn b f)
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverTarget R B C P n hn b f))
  (hw : w.hom ≫ Path.map R (postnikovPerturbedProjection R C n hn) =
    ((cellAugmentation R (cellResolution R P) ≫
      postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedProjection R C n hn) ≫
        Path.diagonal R (postnikov R C n))

def postnikovCellOverClassSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellOverClassComparison R B C P n hn b f
      (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
      (postnikovCellOverNaturality_relative R B C P n hn b f))
    (postnikovCellOverClassComparison R B C P n hn b f w hw) := by
  let z := SquareZero.cellClassWitnessSquare R (postnikovPerturbedProjection R C n hn)
    (postnikovPerturbedProjection_surjective R C n hn)
    (postnikovPerturbedProjection_quasiIso R C n hn)
    (postnikovCellLiftOverNaturalityWitness R B C P n hn b f) w
    (postnikovCellOverNaturality_relative R B C P n hn b f) hw
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovPerturbedClass R C n hn)
    (postnikovPerturbedClass_projection R C n hn)
  refine {
    toWitness := z.toWitness
    source_trace := z.source_trace
    target_trace := z.target_trace
    projection_eq := ?_ }
  exact z.projection_eq.trans (congrArg (fun t =>
    (t ≫ Path.diagonal R (postnikov R C n)) ≫
      Path.diagonal R (Path.algebra R (postnikov R C n)))
    (postnikovCellOverComparison_base R B C P n hn b f))

/-- 同じ元の P 上の class 比較。射影は三重 augmentation そのもの。 -/
def postnikovCellOverCommonComparison : SquareZero.RelativeWitness
    (postnikovCellOverComparisonProjection R P)
    (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))
    (SquareZero.baseChangeLift (b ≫ postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn 1) (postnikovCellOverComparisonProjection R P)
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        (cellAugmentation R (cellResolution R P) ≫
          postnikovCellLiftOverSource R B C P n hn b f) ≫ postnikovPerturbedClass R C n hn)
      (postnikovCellOverClassComparison R B C P n hn b f w hw).source_projection)
    (SquareZero.baseChangeLift (b ≫ postnikovMap R f n)
      (postnikovShiftedLayerBimodule R C n hn 1) (postnikovCellOverComparisonProjection R P)
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        (cellAugmentation R (cellResolution R P) ≫
          postnikovCellLiftOverTarget R B C P n hn b f) ≫ postnikovPerturbedClass R C n hn)
      (postnikovCellOverClassComparison R B C P n hn b f w hw).target_projection) :=
  SquareZero.baseChangeRelativeWitness (b ≫ postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovCellOverComparisonProjection R P)
    (postnikovCellOverClassComparison R B C P n hn b f w hw)

def postnikovCellOverCommonSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellOverCommonComparison R B C P n hn b f
      (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
      (postnikovCellOverNaturality_relative R B C P n hn b f))
    (postnikovCellOverCommonComparison R B C P n hn b f w hw) :=
  SquareZero.baseChangeRelativeWitnessSquare (b ≫ postnikovMap R f n)
    (postnikovShiftedLayerBimodule R C n hn 1) (postnikovCellOverComparisonProjection R P)
    (postnikovCellOverClassSquare R B C P n hn b f w hw)

def postnikovCellOverCommonTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))
      (postnikovCellOverCommonComparison R B C P n hn b f
        (postnikovCellLiftOverNaturalityWitness R B C P n hn b f)
        (postnikovCellOverNaturality_relative R B C P n hn b f)))
    (SquareZeroExtension.transport
      (bimoduleRestrict (b ≫ postnikovMap R f n) (postnikovShiftedLayerBimodule R C n hn 1))
      (postnikovCellOverCommonComparison R B C P n hn b f w hw)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCellOverCommonSquare R B C P n hn b f w hw)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
