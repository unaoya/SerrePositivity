module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellNaturalityComposition

/-!
概要：Postnikov 自然性の二段合成経路を、元の合成射だけで指定した同じ両端へそろえる。
方針：摂動射と切断の厳密な合成則を使い、両端の等式を明示する。
規約：元の合成経路の全射を保持する。使われ方：二因子分解の相対二重比較。
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
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n)
  (h : B ⟶ D) (f : B ⟶ C) (g : C ⟶ D) (heq : f ≫ g = h)

include heq in
lemma postnikovCellLiftFactorization_source :
    postnikovCellLiftCompositionSource R B C D P n hn b f g =
      cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverSource R B D P n hn b h := by
  rw [← heq]
  simp only [postnikovCellLiftCompositionSource, postnikovCellLiftOverSource,
    postnikovPerturbedMap_comp, Category.assoc]

include heq in
lemma postnikovCellLiftFactorization_target :
    postnikovCellLiftCompositionTarget R B C D P n hn b f g =
      cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverTarget R B D P n hn b h := by
  rw [← heq]
  simp only [postnikovCellLiftCompositionTarget, postnikovCellLiftOverTarget,
    postnikovMap_composition, Category.assoc]

def postnikovCellLiftFactorizationWitness : Path.Witness R
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverSource R B D P n hn b h))
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverTarget R B D P n hn b h)) where
  hom := (postnikovCellLiftComposedWitness R B C D P n hn b f g).hom
  source_eq := (postnikovCellLiftComposedWitness R B C D P n hn b f g).source_eq.trans
    (congrArg (fun t => cellAugmentation R (cellResolution R (cellResolution R P)) ≫ t)
      (postnikovCellLiftFactorization_source R B C D P n hn b h f g heq))
  target_eq := (postnikovCellLiftComposedWitness R B C D P n hn b f g).target_eq.trans
    (congrArg (fun t => cellAugmentation R (cellResolution R (cellResolution R P)) ≫ t)
      (postnikovCellLiftFactorization_target R B C D P n hn b h f g heq))

lemma postnikovCellLiftFactorizationWitness_relative :
    (postnikovCellLiftFactorizationWitness R B C D P n hn b h f g heq).hom ≫
      Path.map R (postnikovPerturbedProjection R D n hn) =
    ((cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫
        postnikovCellLiftOverSource R B D P n hn b h)) ≫
      postnikovPerturbedProjection R D n hn) ≫ Path.diagonal R (postnikov R D n) := by
  change (postnikovCellLiftComposedWitness R B C D P n hn b f g).hom ≫ _ = _
  rw [postnikovCellLiftComposedWitness_relative,
    postnikovCellLiftFactorization_source R B C D P n hn b h f g heq]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
