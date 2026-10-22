module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellAugmentation

/-!
概要：元の cell 分解の有限反復と、元の代数への次数全射準同型を明示する。
方針：元の augmentation を順に合成し、全射性と準同型性を帰納する。
規約：cellResolutionMap の関手則を使わない。使われ方：実経路の共通細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

def iteratedCellResolution : ℕ → Mon (Complex R)
  | 0 => A
  | n + 1 => cellResolution R (iteratedCellResolution n)

def iteratedCellAugmentation : (n : ℕ) → iteratedCellResolution R A n ⟶ A
  | 0 => 𝟙 A
  | n + 1 => cellAugmentation R (iteratedCellResolution R A n) ≫ iteratedCellAugmentation n

lemma iteratedCellAugmentation_quasiIso (n : ℕ) :
    QuasiIso (iteratedCellAugmentation R A n).hom := by
  induction n with
  | zero => change QuasiIso (𝟙 A.X); infer_instance
  | succ n ih =>
    change QuasiIso ((cellAugmentation R (iteratedCellResolution R A n)).hom ≫
      (iteratedCellAugmentation R A n).hom)
    exact quasiIso_comp _ _ (hφ := cellAugmentation_quasiIso R _) (hφ' := ih)

lemma iteratedCellAugmentation_epi (n : ℕ) : Epi (iteratedCellAugmentation R A n).hom := by
  induction n with
  | zero => change Epi (𝟙 A.X); infer_instance
  | succ n ih =>
    change Epi ((cellAugmentation R (iteratedCellResolution R A n)).hom ≫
      (iteratedCellAugmentation R A n).hom)
    have := ih
    infer_instance

lemma iteratedCellAugmentation_surjective (n : ℕ) (j : ℤ) :
    Function.Surjective ((iteratedCellAugmentation R A n).hom.f j) := by
  have := iteratedCellAugmentation_epi R A n
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
