module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathOperations
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection

/-!
概要：元の roof の分子を mapping-path の終点へ移し、実左経路を厳密化する模型を作る。
方針：分母には準同型な始点射影を前合成し、右経路は二重 cell 上で接続する。
規約：左経路の存在は別途証明する。使われ方：対角反映後の実逆 roof。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {A B E T : Mon (Complex R)}
  (r : SurjectiveRoof R B A)

def leftPathReplacement : SurjectiveRoof R B A where
  apex := MappingPath.algebra R r.numerator
  denominator := MappingPath.projection R r.numerator ≫ r.denominator
  numerator := MappingPath.target R r.numerator
  denominator_epi := by
    have : Epi (MappingPath.projection R r.numerator).hom :=
      HomologicalComplex.epi_of_epi_f _ (fun n => (ModuleCat.epi_iff_surjective _).2
        (MappingPath.projection_surjective R r.numerator n))
    have := r.denominator_epi
    change Epi ((MappingPath.projection R r.numerator).hom ≫ r.denominator.hom)
    infer_instance
  denominator_quasiIso := quasiIso_comp _ _
    (hφ := MappingPath.projection_quasiIso R r.numerator) (hφ' := r.denominator_quasiIso)

def leftPathReplacementLift (a : T ⟶ r.apex) (b : T ⟶ A)
    (w : Path.Witness R (a ≫ r.numerator) b) : T ⟶ (r.leftPathReplacement R).apex :=
  MappingPath.lift R r.numerator w.hom a w.source_eq

lemma leftPathReplacementLift_denominator (a : T ⟶ r.apex) (b : T ⟶ A)
    (w : Path.Witness R (a ≫ r.numerator) b) :
    r.leftPathReplacementLift R a b w ≫ (r.leftPathReplacement R).denominator =
      a ≫ r.denominator := by
  change MappingPath.lift R r.numerator w.hom a w.source_eq ≫
    (MappingPath.projection R r.numerator ≫ r.denominator) = _
  rw [← Category.assoc, MappingPath.lift_projection]

lemma leftPathReplacementLift_numerator (a : T ⟶ r.apex) (b : T ⟶ A)
    (w : Path.Witness R (a ≫ r.numerator) b) :
    r.leftPathReplacementLift R a b w ≫ (r.leftPathReplacement R).numerator = b :=
  (MappingPath.lift_target R r.numerator w.hom a w.source_eq).trans w.target_eq

def leftPathReplacementRightPath (f : A ⟶ E) (b : B ⟶ E)
    (w : Path.Witness R (r.numerator ≫ f) (r.denominator ≫ b)) : Path.Witness R
    (((r.leftPathReplacement R).cellRefinement R 2).numerator ≫ f)
    (((r.leftPathReplacement R).cellRefinement R 2).denominator ≫ b) := by
  let p := MappingPath.projection R r.numerator
  let v := (MappingPath.pathWitness R r.numerator).postcomp f
  let z := w.precomp p
  let z' : Path.Witness R ((p ≫ r.numerator) ≫ f) ((p ≫ r.denominator) ≫ b) :=
    ⟨z.hom, z.source_eq.trans (Category.assoc _ _ _).symm,
      z.target_eq.trans (Category.assoc _ _ _).symm⟩
  let h := (v.cellReverse R).cellComp R
    (z'.precomp (cellAugmentation R (MappingPath.algebra R r.numerator)))
  exact ⟨h.hom,
    by simpa only [leftPathReplacement, cellRefinement, iteratedCellResolution,
      iteratedCellAugmentation, Category.assoc, Category.comp_id] using h.source_eq,
    by simpa only [leftPathReplacement, cellRefinement, iteratedCellResolution,
      iteratedCellAugmentation, p, Category.assoc, Category.comp_id] using h.target_eq⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
