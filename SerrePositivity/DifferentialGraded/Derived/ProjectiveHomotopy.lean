module
public import SerrePositivity.DifferentialGraded.Derived.HomotopicallyProjective
public import SerrePositivity.DifferentialGraded.Complexes.TowerPrimitives
public import SerrePositivity.DifferentialGraded.Module.Homotopy

/-! # 射影的な始域からacyclic加群への全dg自然なホモトピー -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_homotopy {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleAcyclic A D N)
    (f g : M ⟶ N) : Nonempty (ModuleHomotopy A D f g) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N)
  let zf := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) f)
  let zg := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) g)
  have hz : K.d 0 1 (zf.val - zg.val) = 0 := by
    rw [map_sub, zf.property, zg.property, sub_self]
  obtain ⟨h, dh⟩ := complexAcyclic_boundary (K := K) (hM N hN) 0 (zf.val - zg.val) hz
  exact ⟨⟨h, dh⟩⟩

lemma moduleHomotopicallyProjective_homotopy_map_eq {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleAcyclic A D N)
    (f g : M ⟶ N) : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g :=
  (moduleToHomotopy_map_eq_iff A D f g).2
    (moduleHomotopicallyProjective_homotopy A D hM hN f g)

end SerrePositivity.DifferentialGraded
