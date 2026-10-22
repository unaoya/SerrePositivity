module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellDerivationNaturality
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
概要：元の cell derivation の係数像への障害は、元の比較源上で鎖零ホモトピック。
方針：自然性の実鎖ホモトピーに層射の cokernel を後合成し、源側の係数合成を零化。
規約：底の切断比較が準同型なら比較源も準同型。使われ方：LT の像制限の次の段階。
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

def postnikovClassImageComparisonSource (_hn : 0 ≤ n) :
    cellResolution R (cellResolution R (postnikov R B n)) ⟶ cellResolution R (postnikov R C n) :=
  cellAugmentation R (cellResolution R (postnikov R B n)) ≫
    cellResolutionMap R (postnikovMap R f n)

lemma postnikovClassImageComparisonSource_quasiIso
    (hf : QuasiIso (postnikovMap R f n).hom) :
    QuasiIso (postnikovClassImageComparisonSource R f n hn).hom :=
  quasiIso_comp _ _ (hφ := cellAugmentation_quasiIso R _)
    (hφ' := cellResolutionMap_quasiIso R _ hf)

def postnikovClassImageObstructionHomotopy : Homotopy
    ((postnikovClassImageComparisonSource R f n hn).hom ≫
      (postnikovCellDerivation R C n hn).hom ≫
        cokernel.π (postnikovShiftedLayerMap R B n hn 1 f).hom) 0 := by
  let q := cokernel.π (postnikovShiftedLayerMap R B n hn 1 f).hom
  have h := (postnikovCellDerivationNaturalityHomotopy R f n hn).compRight q
  have hz : ((cellAugmentation R (cellResolution R (postnikov R B n))).hom ≫
      (postnikovCellDerivation R B n hn).hom ≫
        (postnikovShiftedLayerMap R B n hn 1 f).hom) ≫ q = 0 := by
    simp only [Category.assoc, q, cokernel.condition, comp_zero]
  exact h.symm.trans (Homotopy.ofEq hz)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
