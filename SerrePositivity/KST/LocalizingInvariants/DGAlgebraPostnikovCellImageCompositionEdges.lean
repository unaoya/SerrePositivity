module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForward
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineComposition

/-!
概要：元の係数像の二自然性経路を、二段 affine class 合成の指定二辺に全射で同定する。
方針：第一辺は摂動 class の厳密な自然性、第二辺は同じ指定経路の定義を使う。
規約：端点や係数だけの比較ではない。使われ方：元の貼合せへの二因子分解の接続。
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

lemma postnikovCellImageComposition_first_map :
    (postnikovCellImageForwardRelative R B C D P n hn b f g).hom ≫ Path.map R
      (SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
    (SquareZero.relativeClassWitness R (postnikovPerturbedProjection R D n hn)
      (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
      (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
      (postnikovPerturbedClass_projection R D n hn)).hom := by
  rw [postnikovCellImageForwardRelative_map]
  change ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
    Path.map R (postnikovPerturbedClass R C n hn)) ≫
      Path.map R (postnikovDerivationTargetMap R g n hn) =
    ((postnikovCellLiftOverNaturalityWitness R B C P n hn b f).hom ≫
      Path.map R (postnikovPerturbedMap R g n hn)) ≫
        Path.map R (postnikovPerturbedClass R D n hn)
  rw [Category.assoc, ← Path.map_comp, Category.assoc, ← Path.map_comp,
    postnikovPerturbedClass_naturality]

lemma postnikovCellImageComposition_second_map :
    (postnikovCellImageRelative R C D P n hn (b ≫ postnikovMap R f n) g).hom ≫ Path.map R
      (SquareZero.baseChangeMap ((b ≫ postnikovMap R f n) ≫ postnikovMap R g n)
        (postnikovShiftedLayerBimodule R D n hn 1)) =
    (SquareZero.relativeClassSecond R (postnikovPerturbedProjection R D n hn)
      (postnikovCellLiftCompositionFirst R B C D P n hn b f g)
      (postnikovCellLiftCompositionFirst_relative R B C D P n hn b f g)
      (postnikovShiftedLayerBimodule R D n hn 1) (postnikovPerturbedClass R D n hn)
      (postnikovPerturbedClass_projection R D n hn)
      (postnikovCellLiftCompositionSecond R B C D P n hn b f g)
      (postnikovCellLiftCompositionSecond_relative R B C D P n hn b f g)).hom := by
  exact postnikovCellImageRelative_map R C D P n hn (b ≫ postnikovMap R f n) g

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
