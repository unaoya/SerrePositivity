module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassNaturality

/-!
概要：選択した cell derivation の元の係数比較に対する実鎖ホモトピーを回収する。
方針：実 class の相対経路の鎖ホモトピーに、元の係数射影を後合成する。
規約：二重 cell augmentation を保持。使われ方：像係数の cokernel における障害。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ) (hn : 0 ≤ n)

def postnikovCellDerivationNaturalityHomotopy : Homotopy
    ((cellAugmentation R (cellResolution R (postnikov R B n))).hom ≫
      (postnikovCellDerivation R B n hn).hom ≫ (postnikovShiftedLayerMap R B n hn 1 f).hom)
    ((cellAugmentation R (cellResolution R (postnikov R B n))).hom ≫
      (cellResolutionMap R (postnikovMap R f n)).hom ≫ (postnikovCellDerivation R C n hn).hom) := by
  let α := cellAugmentation R (cellResolution R (postnikov R B n))
  let σ : (postnikovDerivationTarget R C n hn).X ⟶
      (postnikovShiftedLayerBimodule R C n hn 1).X := biprod.snd
  have h := (postnikovCellClassNaturalityWitness R f n hn).chainHomotopy.compRight σ
  have hs : (α ≫ postnikovCellClass R B n hn ≫ postnikovDerivationTargetMap R f n hn).hom ≫ σ =
      α.hom ≫ (postnikovCellDerivation R B n hn).hom ≫
        (postnikovShiftedLayerMap R B n hn 1 f).hom := by
    change (α.hom ≫ (postnikovCellClass R B n hn).hom ≫
      (postnikovDerivationTargetMap R f n hn).hom) ≫ σ = _
    rw [Category.assoc, Category.assoc, postnikovDerivationTargetMap_coefficient,
      ← Category.assoc (postnikovCellClass R B n hn).hom, ← postnikovCellDerivation_hom]
  have ht : (α ≫ cellResolutionMap R (postnikovMap R f n) ≫
      postnikovCellClass R C n hn).hom ≫ σ =
      α.hom ≫ (cellResolutionMap R (postnikovMap R f n)).hom ≫
        (postnikovCellDerivation R C n hn).hom := by
    change (α.hom ≫ (cellResolutionMap R (postnikovMap R f n)).hom ≫
      (postnikovCellClass R C n hn).hom) ≫ σ = _
    rw [Category.assoc, Category.assoc, ← postnikovCellDerivation_hom]
  rw [hs, ht] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
