module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationAffine
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeHomProjections
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareComposition

/-!
概要：元の直接自然性を因子分解によらない両端へ移し、二段 affine 合成と実比較する。
方針：直接→cell 合成→affine 合成の二重経路を、元の全射を保って正規化する。
規約：恒等射の自然性の定数性を要求しない。使われ方：分母の直接遷移との比較。
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

def postnikovCellFactorizationDirectWitness :=
  SquareZero.RelativeWitness.transferEndpoints
    (postnikovCellCompositionClassAffine R B C D P n hn b f g)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness_hom R B D P n hn b h C f g heq)
    (postnikovCellCompositionClassDirect R B C D P n hn b f g)

lemma postnikovCellFactorizationDirectWitness_hom :
    (postnikovCellFactorizationDirectWitness R B D P n hn b h C f g heq).hom =
      (postnikovCellCompositionClassDirect R B C D P n hn b f g).hom := by
  let k := SquareZero.RelativeWitness.transferEndpoints_hom
    (postnikovCellCompositionClassAffine R B C D P n hn b f g)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness_hom R B D P n hn b h C f g heq)
    (postnikovCellCompositionClassDirect R B C D P n hn b f g)
  exact k

def postnikovCellFactorizationDirectAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationDirectWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq) :=
  ((postnikovCellCompositionClassSquare R B C D P n hn b f g).trans
    (postnikovCellCompositionAffineSquare R B C D P n hn b f g)).reindex _ _
    (postnikovCellFactorizationDirectWitness_hom R B D P n hn b h C f g heq).symm
    (postnikovCellFactorizationAffineWitness_hom R B D P n hn b h C f g heq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
