module
public import SerrePositivity.DifferentialGraded.Module.Precomposition
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom

/-! # 射影的対象間のquasiIsoによる前合成はHom複体のホモトピー同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleProjectivePrecomposeHomotopyEquiv {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) (T : ModuleCategory A D) :
    HomotopyEquiv (N ⟶[Complex A] T) (M ⟶[Complex A] T) := by
  let Q := moduleToHomotopy A D
  let : IsIso (Q.map f) := moduleHomotopicallyProjective_quasiIso_isIso_homotopy A D hM hN f hf
  let g : N ⟶ M := Q.preimage (inv (Q.map f))
  have hg : Q.map g = inv (Q.map f) := Q.map_preimage _
  have hgf : Nonempty (ModuleHomotopy A D (g ≫ f) (𝟙 N)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (g ≫ f) = Q.map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hfg : Nonempty (ModuleHomotopy A D (f ≫ g) (𝟙 M)) := by
    apply (moduleToHomotopy_map_eq_iff A D _ _).1
    change Q.map (f ≫ g) = Q.map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, hg, IsIso.hom_inv_id, CategoryTheory.Functor.map_id]
  refine
    { hom := eHomWhiskerRight (Complex A) f T
      inv := eHomWhiskerRight (Complex A) g T
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · simpa only [eHomWhiskerRight_comp, eHomWhiskerRight_id] using
      moduleHomPrecomposeHomotopy A D hgf.some T
  · simpa only [eHomWhiskerRight_comp, eHomWhiskerRight_id] using
      moduleHomPrecomposeHomotopy A D hfg.some T

lemma moduleHomotopicallyProjective_precompose_quasiIso {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) (T : ModuleCategory A D) :
    QuasiIso (eHomWhiskerRight (Complex A) f T) :=
  (moduleProjectivePrecomposeHomotopyEquiv A D hM hN f hf T).quasiIso_hom

end SerrePositivity.DifferentialGraded
