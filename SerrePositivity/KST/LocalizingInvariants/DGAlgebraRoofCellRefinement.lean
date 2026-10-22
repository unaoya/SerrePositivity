module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofConnectiveValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellQuasiIsoPathReflection

/-!
概要：実 roof の有限 cell 細分と、準同型の先の経路の実反映を構成する。
方針：元の分母・分子へ同じ全射準同型を前合成し、元の左持ち上げも細分へ持ち上げる。
規約：元の実代数射・両端を保持する。使われ方：class 比較後の乗法的三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {A B C D W : Mon (Complex R)} (r : SurjectiveRoof R A B)

def cellRefinement (n : ℕ) : SurjectiveRoof R A B where
  apex := iteratedCellResolution R r.apex n
  denominator := iteratedCellAugmentation R r.apex n ≫ r.denominator
  numerator := iteratedCellAugmentation R r.apex n ≫ r.numerator
  denominator_epi := by
    have := iteratedCellAugmentation_epi R r.apex n
    have := r.denominator_epi
    change Epi ((iteratedCellAugmentation R r.apex n).hom ≫ r.denominator.hom)
    infer_instance
  denominator_quasiIso := by
    change QuasiIso ((iteratedCellAugmentation R r.apex n).hom ≫ r.denominator.hom)
    exact quasiIso_comp _ _ (hφ := iteratedCellAugmentation_quasiIso R r.apex n)
      (hφ' := r.denominator_quasiIso)

def cellRefinementLift (n : ℕ) (a : W ⟶ r.apex) :
    cellResolution R W ⟶ (cellRefinement R r n).apex :=
  cellResolutionMapLift R a (iteratedCellAugmentation R r.apex n)
    (iteratedCellAugmentation_surjective R r.apex n)
    (iteratedCellAugmentation_quasiIso R r.apex n)

lemma cellRefinementLift_augmentation (n : ℕ) (a : W ⟶ r.apex) :
    cellRefinementLift R r n a ≫ iteratedCellAugmentation R r.apex n =
      cellAugmentation R W ≫ a := cellResolutionMapLift_projection R _ _ _ _

lemma cellRefinementLift_denominator (n : ℕ) (a : W ⟶ r.apex) :
    cellRefinementLift R r n a ≫ (cellRefinement R r n).denominator =
      cellAugmentation R W ≫ a ≫ r.denominator := by
  change cellRefinementLift R r n a ≫
    (iteratedCellAugmentation R r.apex n ≫ r.denominator) = _
  rw [← Category.assoc, cellRefinementLift_augmentation, Category.assoc]

lemma cellRefinementLift_numerator (n : ℕ) (a : W ⟶ r.apex) :
    cellRefinementLift R r n a ≫ (cellRefinement R r n).numerator =
      cellAugmentation R W ≫ a ≫ r.numerator := by
  change cellRefinementLift R r n a ≫
    (iteratedCellAugmentation R r.apex n ≫ r.numerator) = _
  rw [← Category.assoc, cellRefinementLift_augmentation, Category.assoc]

def cellReflectEquation (f : B ⟶ C) (g : A ⟶ C) (p : C ⟶ D) (hp : QuasiIso p.hom)
    (w : Path.Witness R ((r.numerator ≫ f) ≫ p) ((r.denominator ≫ g) ≫ p)) :
    Path.Witness R ((cellRefinement R r 4).numerator ≫ f)
      ((cellRefinement R r 4).denominator ≫ g) := by
  let v := Path.Witness.cellReflectQuasiIso R p hp w
  exact { hom := v.hom
          source_eq := by simpa only [cellRefinement, Category.assoc] using v.source_eq
          target_eq := by simpa only [cellRefinement, Category.assoc] using v.target_eq }

section Value
universe v w
variable {E : Type v} [Category.{w} E] (L : Mon (Complex R) ⥤ E)

lemma cellRefinement_value (hL : InvertsQuasiIsos R L) (n : ℕ) :
    value R L hL (cellRefinement R r n) = value R L hL r := by
  have := hL (cellRefinement R r n).denominator (cellRefinement R r n).denominator_quasiIso
  have he : L.map (cellRefinement R r n).denominator ≫ value R L hL r =
      L.map (cellRefinement R r n).numerator := by
    change L.map (iteratedCellAugmentation R r.apex n ≫ r.denominator) ≫ _ =
      L.map (iteratedCellAugmentation R r.apex n ≫ r.numerator)
    rw [L.map_comp, L.map_comp, Category.assoc, denominator_value]
  apply (cancel_epi (L.map (cellRefinement R r n).denominator)).1
  exact (denominator_value R L hL (cellRefinement R r n)).trans he.symm

lemma cellRefinement_connectiveValue (hL : InvertsConnectiveQuasiIsos R L)
    (hA : IsConnective R A) (n : ℕ) :
    connectiveValue R L hL hA (cellRefinement R r n) = connectiveValue R L hL hA r := by
  have := hL (apex_isConnective R (cellRefinement R r n) hA) hA
    (cellRefinement R r n).denominator (cellRefinement R r n).denominator_quasiIso
  have he : L.map (cellRefinement R r n).denominator ≫ connectiveValue R L hL hA r =
      L.map (cellRefinement R r n).numerator := by
    change L.map (iteratedCellAugmentation R r.apex n ≫ r.denominator) ≫ _ =
      L.map (iteratedCellAugmentation R r.apex n ≫ r.numerator)
    rw [L.map_comp, L.map_comp, Category.assoc, denominator_connectiveValue]
  apply (cancel_epi (L.map (cellRefinement R r n).denominator)).1
  exact (denominator_connectiveValue R L hL hA (cellRefinement R r n)).trans he.symm

end Value

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
