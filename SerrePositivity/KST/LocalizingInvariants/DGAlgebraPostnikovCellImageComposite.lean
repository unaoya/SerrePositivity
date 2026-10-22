module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageCompositionEdges

/-!
概要：元の二つの係数像自然性経路を同じ P 上で affine 合成し、中点の全 class 射を同定する。
方針：第一辺の target 評価で、中点を元の摂動中点の class 像へ戻す。
規約：両自然性経路そのものを使用。使われ方：二段 affine 合成の全経路同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (f : B ⟶ C) (g : C ⟶ D)

def postnikovCellImageComposite : SquareZero.RelativeWitness
    (cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P)
    (bimoduleRestrict ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
      (postnikovShiftedLayerBimodule R D n hn 1))
    ((cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R B P n hn b ≫
      SquareZero.coefficientMap P (postnikovCellClassOverCoefficient R B C P n hn b f)) ≫
      postnikovCellImageForwardMap R B C D P n hn b f g)
    (cellAugmentation R (cellResolution R P) ≫ postnikovCellClassOver R D P n hn
      ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)) :=
  (postnikovCellImageForwardRelative R B C D P n hn b f g).comp
    (postnikovCellImageRelative R C D P n hn (b ≫ postnikovMap R f n) g)

lemma postnikovCellImageComposition_middle_map :
    (cellAugmentation R (cellResolution R P) ≫
      postnikovCellClassOver R C P n hn (b ≫ postnikovMap R f n) ≫
        postnikovCellImageForwardMap R B C D P n hn b f g) ≫
      SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1) =
    postnikovCellLiftCompositionMiddle R B C D P n hn b f g ≫
      postnikovPerturbedClass R D n hn := by
  have h := congrArg (fun t => t ≫ Path.target R (postnikovDerivationTarget R D n hn))
    (postnikovCellImageComposition_first_map R B C D P n hn b f g)
  change ((postnikovCellImageForwardRelative R B C D P n hn b f g).hom ≫ Path.map R _) ≫
    Path.target R _ =
    ((postnikovCellLiftCompositionFirst R B C D P n hn b f g).hom ≫
      Path.map R (postnikovPerturbedClass R D n hn)) ≫ Path.target R _ at h
  simpa only [Category.assoc, Path.map_target,
    reassoc_of% (postnikovCellImageForwardRelative R B C D P n hn b f g).target_eq,
    reassoc_of% (postnikovCellLiftCompositionFirst R B C D P n hn b f g).target_eq] using h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
