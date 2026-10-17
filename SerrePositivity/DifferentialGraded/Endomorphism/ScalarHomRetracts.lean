module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomNaturality
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.Algebra.Homology.QuasiIso

/-! # 実際のHom係数変更比較と始域のretract -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]

def scalarModuleHom_retractArrow {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D) :
    RetractArrow
      (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) P))
      (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
        (ForgetEnrichment.to (Complex A) P)) where
  i := Arrow.homMk
    ((ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.r P))
    (eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.r)
      ((ScalarExtension.moduleExtension φ D).obj P))
    (scalarModuleHom_precompose φ D r.r P)
  r := Arrow.homMk
    ((ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.i P))
    (eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.i)
      ((ScalarExtension.moduleExtension φ D).obj P))
    (scalarModuleHom_precompose φ D r.i P)
  retract := by
    apply Arrow.hom_ext
    · change (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.r P) ≫
        (ScalarExtension.extension φ).map (eHomWhiskerRight (Complex A) r.i P) = 𝟙 _
      rw [← CategoryTheory.Functor.map_comp, ← eHomWhiskerRight_comp, r.retract,
        eHomWhiskerRight_id, CategoryTheory.Functor.map_id]
    · change eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.r)
          ((ScalarExtension.moduleExtension φ D).obj P) ≫
        eHomWhiskerRight (Complex A') ((ScalarExtension.moduleExtension φ D).map r.i)
          ((ScalarExtension.moduleExtension φ D).obj P) = 𝟙 _
      rw [← eHomWhiskerRight_comp, ← CategoryTheory.Functor.map_comp, r.retract,
        CategoryTheory.Functor.map_id, eHomWhiskerRight_id]

lemma scalarModuleHom_isIso_of_retract {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D)
    (hN : IsIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    IsIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) :=
  MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (Complex A'))
    (scalarModuleHom_retractArrow φ D r P) hN

lemma scalarModuleHom_quasiIso_of_retract {M N : ModuleCategory A D} (r : Retract M N)
    (P : ModuleCategory A D)
    (hN : QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) N)
      (ForgetEnrichment.to (Complex A) P))) :
    QuasiIso (scalarModuleHom φ D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) P)) :=
  MorphismProperty.of_retract (P := HomologicalComplex.quasiIso (ModuleCat A') (.up ℤ))
    (scalarModuleHom_retractArrow φ D r P) hN

end SerrePositivity.DifferentialGraded
