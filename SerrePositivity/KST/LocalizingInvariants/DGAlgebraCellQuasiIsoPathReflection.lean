module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：任意の準同型の先にある実経路を、四重 cell 細分上で元の代数へ反映する。
方針：元の MappingPath の全射準同型 target で反映し、元の projection へ後合成。
規約：元の準同型に次数全射性を要求しない。使われ方：元の roof の三角形反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A C B : Mon (Complex R)} (p : C ⟶ B)
  (hq : QuasiIso p.hom) {f g : A ⟶ C} (w : Path.Witness R (f ≫ p) (g ≫ p))

def Path.Witness.cellReflectQuasiIso : Path.Witness R
    (iteratedCellAugmentation R A 4 ≫ f) (iteratedCellAugmentation R A 4 ≫ g) := by
  let w' : Path.Witness R
      ((f ≫ MappingPath.section_ R p) ≫ MappingPath.target R p)
      ((g ≫ MappingPath.section_ R p) ≫ MappingPath.target R p) :=
    { hom := w.hom
      source_eq := by simpa only [Category.assoc, MappingPath.section_target] using w.source_eq
      target_eq := by simpa only [Category.assoc, MappingPath.section_target] using w.target_eq }
  let v := (Path.Witness.cellReflectSurjective R (MappingPath.target R p)
    (MappingPath.target_surjective R p) (MappingPath.target_quasiIso R p hq) w').postcomp
      (MappingPath.projection R p)
  exact { hom := v.hom
          source_eq := by
            simpa only [Category.assoc, MappingPath.section_projection, Category.comp_id]
              using v.source_eq
          target_eq := by
            simpa only [Category.assoc, MappingPath.section_projection, Category.comp_id]
              using v.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
