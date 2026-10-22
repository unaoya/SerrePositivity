module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLiftNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMap

/-!
概要：任意の底射に沿う二つの Postnikov cell lift を、同じ底上の実相対経路で比較する。
方針：両射影を元の augmentation と底射の合成へ照合し、全射準同型上で cell 経路を作る。
規約：二重 cell augmentation を前合成。使われ方：共通底の class 自然性。
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

abbrev postnikovCellLiftOverSource := cellResolutionMap R b ≫
  postnikovCellLift R B n hn ≫ postnikovPerturbedMap R f n hn

abbrev postnikovCellLiftOverTarget := cellResolutionMap R (b ≫ postnikovMap R f n) ≫
  postnikovCellLift R C n hn

lemma postnikovCellLiftOverSource_projection : postnikovCellLiftOverSource R B C P n hn b f ≫
    postnikovPerturbedProjection R C n hn = cellAugmentation R P ≫ b ≫ postnikovMap R f n := by
  simp only [postnikovCellLiftOverSource, Category.assoc]
  rw [postnikovPerturbedProjection_naturality,
    reassoc_of% (postnikovCellLift_projection R B n hn),
    reassoc_of% (cellResolutionMap_augmentation R b)]

lemma postnikovCellLiftOverTarget_projection : postnikovCellLiftOverTarget R B C P n hn b f ≫
    postnikovPerturbedProjection R C n hn = cellAugmentation R P ≫ b ≫ postnikovMap R f n := by
  rw [postnikovCellLiftOverTarget, Category.assoc, postnikovCellLift_projection,
    cellResolutionMap_augmentation]

lemma postnikovCellLiftOver_projection : postnikovCellLiftOverSource R B C P n hn b f ≫
    postnikovPerturbedProjection R C n hn = postnikovCellLiftOverTarget R B C P n hn b f ≫
      postnikovPerturbedProjection R C n hn :=
  (postnikovCellLiftOverSource_projection R B C P n hn b f).trans
    (postnikovCellLiftOverTarget_projection R B C P n hn b f).symm

def postnikovCellLiftOverNaturalityWitness : Path.Witness R
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverSource R B C P n hn b f)
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverTarget R B C P n hn b f) :=
  RelativePath.cellPathWitness R (postnikovPerturbedProjection R C n hn)
    (postnikovPerturbedProjection_surjective R C n hn)
    (postnikovPerturbedProjection_quasiIso R C n hn)
    (postnikovCellLiftOverSource R B C P n hn b f) (postnikovCellLiftOverTarget R B C P n hn b f)
    (postnikovCellLiftOver_projection R B C P n hn b f)

lemma postnikovCellLiftOverNaturalityWitness_relative :
    (postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (postnikovPerturbedProjection R C n hn) =
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P ≫ b ≫ postnikovMap R f n) ≫
      Path.diagonal R (postnikov R C n) :=
  (RelativePath.cellPathWitness_relative R _ _ _ _ _ _).trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R C n))
      (congrArg (fun t => cellAugmentation R (cellResolution R P) ≫ t)
        (postnikovCellLiftOverSource_projection R B C P n hn b f)))

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
