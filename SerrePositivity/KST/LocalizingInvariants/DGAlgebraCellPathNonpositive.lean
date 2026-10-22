module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellComparisonPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverSurjective

/-!
概要：cell 比較に反映した元の経路を、準同型な非正次数共通源上へ移す。
方針：反復 cell 源の connective 性を示し、実 connective cover を前合成する。
規約：元の源への射の準同型性も証明。使われ方：零底経路の厳密な相対化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma iteratedCellResolution_isConnective (A : Mon (Complex R)) (hA : IsConnective R A) (n : ℕ) :
    IsConnective R (iteratedCellResolution R A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact cellResolution_isConnective R _ ih

def cellPathNonpositiveSource (A : Mon (Complex R)) : Mon (Complex R) :=
  connectiveCover R (iteratedCellResolution R (cellResolution R A) 4)

instance cellPathNonpositiveSource_nonpositive (A : Mon (Complex R)) :
    (cellPathNonpositiveSource R A).X.IsStrictlyLE 0 := by
  change (coverComplex R _).IsStrictlyLE 0
  infer_instance

def cellPathNonpositiveProjection (A : Mon (Complex R)) : cellPathNonpositiveSource R A ⟶ A :=
  connectiveCoverInclusion R _ ≫ iteratedCellAugmentation R (cellResolution R A) 4 ≫
    cellAugmentation R A

lemma cellPathNonpositiveProjection_quasiIso (A : Mon (Complex R)) (hA : IsConnective R A) :
    QuasiIso (cellPathNonpositiveProjection R A).hom :=
  quasiIso_comp _ _
    (hφ := connectiveCoverInclusion_quasiIso R _
      (iteratedCellResolution_isConnective R _ (cellResolution_isConnective R A hA) 4))
    (hφ' := quasiIso_comp _ _ (hφ := iteratedCellAugmentation_quasiIso R _ 4)
      (hφ' := cellAugmentation_quasiIso R A))

lemma cellPathNonpositiveProjection_surjective (A : Mon (Complex R)) [A.X.IsStrictlyLE 0]
    (n : ℤ) : Function.Surjective ((cellPathNonpositiveProjection R A).hom.f n) := by
  let p : iteratedCellResolution R (cellResolution R A) 4 ⟶ A :=
    iteratedCellAugmentation R (cellResolution R A) 4 ≫ cellAugmentation R A
  have hp : QuasiIso p.hom := quasiIso_comp _ _
    (hφ := iteratedCellAugmentation_quasiIso R _ 4) (hφ' := cellAugmentation_quasiIso R A)
  have hs (j : ℤ) : Function.Surjective (p.hom.f j) :=
    (cellAugmentation_surjective R A j).comp
      (iteratedCellAugmentation_surjective R (cellResolution R A) 4 j)
  exact connectiveCoverInclusion_comp_surjective R p hs hp n

def cellPathNonpositiveComparison {A B : Mon (Complex R)} (f : A ⟶ B) :
    cellPathNonpositiveSource R A ⟶ cellResolution R B :=
  connectiveCoverInclusion R _ ≫ iteratedCellAugmentation R (cellResolution R A) 4 ≫
    cellResolutionMap R f

lemma cellPathNonpositiveComparison_projection {A B : Mon (Complex R)} (f : A ⟶ B) :
    cellPathNonpositiveComparison R f ≫ cellAugmentation R B =
      cellPathNonpositiveProjection R A ≫ f := by
  simp only [cellPathNonpositiveComparison, cellPathNonpositiveProjection, Category.assoc]
  exact congrArg (fun t => connectiveCoverInclusion R _ ≫
    iteratedCellAugmentation R (cellResolution R A) 4 ≫ t) (cellResolutionMap_augmentation R f)

def cellPathNonpositiveWitness {A B : Mon (Complex R)} {f g : A ⟶ B}
    (w : Path.Witness R f g) :
    Path.Witness R (cellPathNonpositiveComparison R f) (cellPathNonpositiveComparison R g) :=
  (cellResolutionMapPathWitness R w).precomp (connectiveCoverInclusion R _)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
