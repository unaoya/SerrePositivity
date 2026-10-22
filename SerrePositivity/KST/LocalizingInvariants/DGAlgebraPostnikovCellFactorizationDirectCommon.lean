module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationDirect
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationImagePath

/-!
概要：直接自然性と二段 affine 合成の実比較を、同じ P の底変更係数上へ移す。
方針：直接経路の全射を元の単一自然性で表示し、元の底変更 pullback を使う。
規約：同じ四重 cell 源と P 射影を保持。使われ方：元の直接遷移の ImageWitness 比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

lemma postnikovCellFactorizationDirectClass_hom :
    (postnikovCellFactorizationDirectWitness R B D P n hn b h C f g heq).hom =
    postnikovCellImageToSecond R P ≫
      (postnikovCellClassOverNaturalityWitness R B D P n hn b h).hom := by
  rw [postnikovCellFactorizationDirectWitness_hom]
  change (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (postnikovCellLiftOverNaturalityWitness R B D P n hn b (f ≫ g)).hom)) ≫
        Path.map R (postnikovPerturbedClass R D n hn) = _
  rw [heq]
  simp only [postnikovCellImageToSecond, postnikovCellClassOverNaturalityWitness,
    Path.Witness.postcomp, Category.assoc]

def postnikovCellFactorizationDirectCommonWitness :=
  SquareZero.baseChangeRelativeWitness (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationDirectWitness R B D P n hn b h C f g heq)

def postnikovCellFactorizationDirectAffineCommonSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationDirectCommonWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineCommonWitness R B D P n hn b h C f g heq) :=
  SquareZero.baseChangeRelativeWitnessSquare (b ≫ postnikovMap R h n)
    (postnikovShiftedLayerBimodule R D n hn 1) (postnikovCellFactorizationProjection R P)
    (postnikovCellFactorizationDirectAffineSquare R B D P n hn b h C f g heq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
