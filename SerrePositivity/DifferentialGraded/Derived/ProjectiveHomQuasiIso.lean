module
public import SerrePositivity.DifferentialGraded.Module.HomConeIso
public import SerrePositivity.DifferentialGraded.Derived.SemifreeProjective

/-! # 射影的始域からの全Homは指定quasiIsoを保つ -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_postcompose_quasiIso {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) : QuasiIso (eHomWhiskerLeft (Complex A) T f) := by
  apply (complex_quasiIso_iff_acyclic_cone A _).2
  intro q
  exact (hT (moduleCone A D f) ((moduleQuasiIso_iff_acyclic_cone A D f).1 hf) q).of_iso
    (moduleHomConeIso A D T f).symm

lemma moduleSemifree_postcompose_quasiIso {T M N : ModuleCategory A D}
    (hT : moduleSemifree A D T) (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso (eHomWhiskerLeft (Complex A) T f) :=
  moduleHomotopicallyProjective_postcompose_quasiIso A D
    (moduleSemifree_homotopicallyProjective A D hT) f hf

end SerrePositivity.DifferentialGraded
