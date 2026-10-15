module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso
public import SerrePositivity.DifferentialGraded.Module.HomCycles
public import SerrePositivity.DifferentialGraded.Complexes.QuasiIsoCycles

/-! # 射影的始域からquasiIsoに沿うホモトピーまでの持ち上げと一意性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_homotopy_lift {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (g : T ⟶ N) :
    ∃ s : T ⟶ M, Nonempty (ModuleHomotopy A D (s ≫ f) g) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
  let L := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) N)
  let r : K ⟶ L := eHomWhiskerLeft (Complex A) T f
  have hr : QuasiIso r := moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  let z := cycleFromUnit L (ForgetEnrichment.homTo (Complex A) g)
  have hl := complexQuasiIso_cycle_lift (K := K) (L := L) A r hr (-1)
  rw [show (-1 : ℤ) + 1 = 0 by omega, show (0 : ℤ) + 1 = 1 by omega] at hl
  obtain ⟨a, ha, b, hb⟩ := hl z.val z.property
  let s : T ⟶ M := moduleMorphismOfCycle A D a ha
  have hsf : r.f 0 a =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val := by
    calc
      r.f 0 a = r.f 0
          (cycleFromUnit K (ForgetEnrichment.homTo (Complex A) s)).val :=
        congrArg (r.f 0) (moduleMorphismOfCycle_cycle A D (M := T) (N := M) a ha).symm
      _ = _ := moduleHomCycle_postcompose A D s f
  refine ⟨s, ⟨⟨-b, ?_⟩⟩⟩
  change L.d (-1) 0 (-b) =
    (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val - z.val
  rw [map_neg, hb, hsf, neg_sub]

lemma moduleHomotopicallyProjective_homotopy_reflect {T M N : ModuleCategory A D}
    (hT : moduleHomotopicallyProjective A D T) (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) (s t : T ⟶ M)
    (h : ModuleHomotopy A D (s ≫ f) (t ≫ f)) : Nonempty (ModuleHomotopy A D s t) := by
  let K := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) M)
  let L := moduleHom A D (ForgetEnrichment.to (Complex A) T)
    (ForgetEnrichment.to (Complex A) N)
  let r : K ⟶ L := eHomWhiskerLeft (Complex A) T f
  have hr : QuasiIso r := moduleHomotopicallyProjective_postcompose_quasiIso A D hT f hf
  let zs := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) s)
  let zt := cycleFromUnit K (ForgetEnrichment.homTo (Complex A) t)
  let a := zs.val - zt.val
  have ha : K.d 0 1 a = 0 := by rw [map_sub, zs.property, zt.property, sub_self]
  have hs : r.f 0 zs.val =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val :=
    moduleHomCycle_postcompose A D s f
  have ht : r.f 0 zt.val =
      (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (t ≫ f))).val :=
    moduleHomCycle_postcompose A D t f
  have hb : L.d (-1) 0 h.val = r.f 0 a := by
    calc
      L.d (-1) 0 h.val =
          (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (s ≫ f))).val -
            (cycleFromUnit L (ForgetEnrichment.homTo (Complex A) (t ≫ f))).val := h.property
      _ = r.f 0 zs.val - r.f 0 zt.val := congrArg₂ (fun x y : L.X 0 => x - y) hs.symm ht.symm
      _ = r.f 0 a := (map_sub _ _ _).symm
  have hl := complexQuasiIso_boundary_reflect (K := K) (L := L) A r hr (-1)
  rw [show (-1 : ℤ) + 1 = 0 by omega, show (0 : ℤ) + 1 = 1 by omega] at hl
  obtain ⟨u, hu⟩ := hl a ha h.val hb
  exact ⟨⟨u, hu⟩⟩

end SerrePositivity.DifferentialGraded
