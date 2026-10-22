module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellNaturalityComposition

/-!
概要：同じ合成射の二つの因子分解に対し、直接 class 自然性の全経路が一致する。
方針：直接経路が元の合成射の指定自然性経路そのものであることを展開する。
規約：合成した経路同士の厳密一致は主張しない。使われ方：右自然性正方形の共通基準。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B C C' D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] [C'.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n)
  (f : B ⟶ C) (g : C ⟶ D) (f' : B ⟶ C') (g' : C' ⟶ D)
  (heq : f ≫ g = f' ≫ g')

include heq in
lemma postnikovCellCompositionClassDirect_hom_congr :
    (postnikovCellCompositionClassDirect R B C D P n hn b f g).hom =
      (postnikovCellCompositionClassDirect R B C' D P n hn b f' g').hom := by
  change (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (postnikovCellLiftOverNaturalityWitness R B D P n hn b (f ≫ g)).hom) ≫
        Path.map R (postnikovPerturbedClass R D n hn)) =
    (cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (postnikovCellLiftOverNaturalityWitness R B D P n hn b (f' ≫ g')).hom) ≫
        Path.map R (postnikovPerturbedClass R D n hn))
  rw [heq]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
