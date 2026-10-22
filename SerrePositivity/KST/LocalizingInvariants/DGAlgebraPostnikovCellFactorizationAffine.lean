module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellAffineComposition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareReindex
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCellClassWitnessHom

/-!
概要：二段の affine class 経路を、合成射だけに依存する同じ両端と底へ移す。
方針：元の cell 合成との二重比較を保ち、端点と底の等式だけを変更する。
規約：全経路を選び直さない。使われ方：二因子分解の affine 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)
  (C : Mon (Complex R)) [C.X.IsStrictlyLE 0]
  (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

include heq in
lemma postnikovCellFactorizationAffine_source :
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
          postnikovPerturbedClass R D n hn =
      postnikovCellFactorizationSource R B D P n hn b h := by
  rw [postnikovCellLiftFactorization_source R B C D P n hn b h f g heq]
  rfl

include heq in
lemma postnikovCellFactorizationAffine_target :
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionTarget R B C D P n hn b f g) ≫
          postnikovPerturbedClass R D n hn =
      postnikovCellFactorizationTarget R B D P n hn b h := by
  rw [postnikovCellLiftFactorization_target R B C D P n hn b h f g heq]
  rfl

include heq in
lemma postnikovCellFactorizationAffine_base :
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        postnikovCellLiftCompositionSource R B C D P n hn b f g) ≫
          postnikovPerturbedProjection R D n hn =
      postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n) := by
  rw [postnikovCellLiftFactorization_source R B C D P n hn b h f g heq]
  exact postnikovCellFactorization_base R B D P n hn b h

def postnikovCellFactorizationAffineWitness : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n))
    (postnikovShiftedLayerBimodule R D n hn 1)
    (postnikovCellFactorizationSource R B D P n hn b h)
    (postnikovCellFactorizationTarget R B D P n hn b h) where
  hom := (postnikovCellCompositionClassAffine R B C D P n hn b f g).hom
  source_eq := (postnikovCellCompositionClassAffine R B C D P n hn b f g).source_eq.trans
    (postnikovCellFactorizationAffine_source R B D P n hn b h C f g heq)
  target_eq := (postnikovCellCompositionClassAffine R B C D P n hn b f g).target_eq.trans
    (postnikovCellFactorizationAffine_target R B D P n hn b h C f g heq)
  projection_eq := (postnikovCellCompositionClassAffine R B C D P n hn b f g).projection_eq.trans
    (congrArg (fun t => t ≫ Path.diagonal R (postnikov R D n))
      (postnikovCellFactorizationAffine_base R B D P n hn b h C f g heq))

lemma postnikovCellFactorizationClassWitness_hom :
    (postnikovCellCompositionClassComposed R B C D P n hn b f g).hom =
      (postnikovCellFactorizationClassWitness R B D P n hn b h C f g heq).hom := by
  rw [postnikovCellCompositionClassComposed, postnikovCellFactorizationClassWitness,
    SquareZero.RelativeWitness.rebase_hom, SquareZero.cellClassWitness_hom,
    SquareZero.cellClassWitness_hom]
  rfl

lemma postnikovCellFactorizationAffineWitness_hom :
    (postnikovCellCompositionClassAffine R B C D P n hn b f g).hom =
      (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq).hom := rfl

/-- 元の cell class と同じ両端・底の affine 経路との実二重比較。 -/
def postnikovCellFactorizationAffineSquare : SquareZero.RelativeWitnessSquare
    (postnikovCellFactorizationClassWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq) := by
  exact (postnikovCellCompositionAffineSquare R B C D P n hn b f g).reindex
    (postnikovCellFactorizationClassWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness R B D P n hn b h C f g heq)
    (postnikovCellFactorizationClassWitness_hom R B D P n hn b h C f g heq)
    (postnikovCellFactorizationAffineWitness_hom R B D P n hn b h C f g heq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
