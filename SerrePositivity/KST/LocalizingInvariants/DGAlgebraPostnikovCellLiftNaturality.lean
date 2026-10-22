module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：選択した Postnikov の cell lift の自然性を、実相対経路で比較する。
方針：両比較を同じ全射準同型な射影上で一致させ、もう一度 cell 分解上で持ち上げる。
規約：cell 比較の厳密な関手則を仮定しない。使われ方：元の cell class の像への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovCellLift_naturality_projection :
    (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn) ≫
      postnikovPerturbedProjection R C n hn =
        (cellResolutionMap R (postnikovMap R f n) ≫ postnikovCellLift R C n hn) ≫
          postnikovPerturbedProjection R C n hn := by
  rw [Category.assoc, postnikovPerturbedProjection_naturality, ← Category.assoc,
    postnikovCellLift_projection, Category.assoc, postnikovCellLift_projection,
    cellResolutionMap_augmentation]

def postnikovCellLiftNaturalityWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
      (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn))
    (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
      (cellResolutionMap R (postnikovMap R f n) ≫ postnikovCellLift R C n hn)) :=
  RelativePath.cellPathWitness R (postnikovPerturbedProjection R C n hn)
    (postnikovPerturbedProjection_surjective R C n hn)
    (postnikovPerturbedProjection_quasiIso R C n hn)
    (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn)
    (cellResolutionMap R (postnikovMap R f n) ≫ postnikovCellLift R C n hn)
    (postnikovCellLift_naturality_projection R f n hn)

lemma postnikovCellLiftNaturalityWitness_relative :
    (postnikovCellLiftNaturalityWitness R f n hn).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
        (cellAugmentation R (cellResolution R (postnikov R B n)) ≫
          (postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn) ≫
            postnikovPerturbedProjection R C n hn) ≫ Path.diagonal R (postnikov R C n) :=
  RelativePath.cellPathWitness_relative R _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
