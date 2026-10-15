module
public import SerrePositivity.DifferentialGraded.Module.Postcomposition
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 主Hom endの閉次数零要素と加群射の合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleMorphismOfCycle {M N : ModuleCategory A D}
    (z : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).X 0)
    (hz : (moduleHom A D (ForgetEnrichment.to (Complex A) M)
      (ForgetEnrichment.to (Complex A) N)).d 0 1 z = 0) : M ⟶ N :=
  (closedHomEquiv A (RightModule A D) M N).symm ⟨z, hz⟩

lemma moduleMorphismOfCycle_cycle {M N : ModuleCategory A D} (z) (hz) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      (moduleMorphismOfCycle A D (M := M) (N := N) z hz))).val = z :=
  congrArg Subtype.val ((closedHomEquiv A (RightModule A D) M N).apply_symm_apply ⟨z, hz⟩)

lemma moduleHomCycle_postcompose {T M N : ModuleCategory A D} (g : T ⟶ M) (f : M ⟶ N) :
    (eHomWhiskerLeft (Complex A) T f).f 0
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) g)).val =
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A) (g ≫ f))).val := by
  apply moduleHomElement_ext A D (M := ForgetEnrichment.to (Complex A) T)
    (N := ForgetEnrichment.to (Complex A) N)
  intro x
  rw [moduleHomWhiskerLeft_apply_π, ← moduleEvaluation_cochain A D x g,
    ← moduleEvaluation_cochain A D x (g ≫ f), CategoryTheory.Functor.map_comp,
    Cochain.ofHom_comp]

end SerrePositivity.DifferentialGraded
