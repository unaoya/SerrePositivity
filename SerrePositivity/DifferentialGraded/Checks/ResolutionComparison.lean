module
public import SerrePositivity.DifferentialGraded.Derived.ResolutionComparison

/-! # U10b6f：解像度の比較と選択独立性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example {P Q M : ModuleCategory A D} (hP : moduleSemifree A D P) (hQ : moduleSemifree A D Q)
    (p : P ⟶ M) (q : Q ⟶ M) (hp : moduleQuasiIso A D p) (hq : moduleQuasiIso A D q) :
    ∃ s : P ⟶ Q, moduleQuasiIso A D s ∧
      (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
        (moduleToHomotopy A D).map p ∧ IsIso ((moduleToHomotopy A D).map s) :=
  moduleSemifreeResolution_comparison A D hP hQ p q hp hq

example {P Q M : ModuleCategory A D} (hP : moduleHomotopicallyProjective A D P)
    (p : P ⟶ M) (q : Q ⟶ M) (hq : moduleQuasiIso A D q) (s t : P ⟶ Q)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p)
    (ht : (moduleToHomotopy A D).map t ≫ (moduleToHomotopy A D).map q =
      (moduleToHomotopy A D).map p) :
    (moduleToHomotopy A D).map s = (moduleToHomotopy A D).map t :=
  moduleProjectiveResolution_comparison_unique A D hP p q hq s t hs ht

example {P M : ModuleCategory A D} (hP : moduleHomotopicallyProjective A D P)
    (p : P ⟶ M) (hp : moduleQuasiIso A D p) (s : P ⟶ P)
    (hs : (moduleToHomotopy A D).map s ≫ (moduleToHomotopy A D).map p =
      (moduleToHomotopy A D).map p) : (moduleToHomotopy A D).map s = 𝟙 _ := by
  have hi : (moduleToHomotopy A D).map (𝟙 P) ≫ (moduleToHomotopy A D).map p =
      (moduleToHomotopy A D).map p := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (moduleProjectiveResolution_comparison_unique A D hP p p hp s (𝟙 P) hs hi).trans
    ((moduleToHomotopy A D).map_id P)

end SerrePositivity.DifferentialGraded.Checks

open SerrePositivity.DifferentialGraded
#print axioms moduleProjectiveResolution_comparison
#print axioms moduleSemifreeResolution_comparison
#print axioms moduleProjectiveResolution_comparison_unique
#print axioms moduleProjectiveResolution_comparison_cocycle
