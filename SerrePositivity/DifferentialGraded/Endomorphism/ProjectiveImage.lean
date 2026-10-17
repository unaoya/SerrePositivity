module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomotopyImage
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveCriterion
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations

/-! # 指定対象のthick閉包のHom像のホモトピー射影性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleHomotopyProjectiveLocus : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun X => moduleHomotopicallyProjective A D X.as

instance moduleHomotopyProjectiveLocusStableUnderRetracts :
    (moduleHomotopyProjectiveLocus A D).IsStableUnderRetracts where
  of_retract {X Y} a hY := by
    obtain ⟨i, hi⟩ := (moduleToHomotopy A D).map_surjective a.i
    obtain ⟨r, hr⟩ := (moduleToHomotopy A D).map_surjective a.r
    apply moduleHomotopicallyProjective_of_homotopyRetract A D i r _ hY
    rw [CategoryTheory.Functor.map_comp, hi, hr, a.retract]
    exact ((moduleToHomotopy A D).map_id X.as).symm

instance moduleHomotopyProjectiveLocusStableUnderShift :
    (moduleHomotopyProjectiveLocus A D).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨fun X hX =>
    (moduleHomotopyProjectiveLocus A D).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
      (moduleHomotopicallyProjective_shift A D hX s)⟩

lemma moduleHomotopyProjectiveLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D)) (hT : T ∈ distTriang _)
    (h₁ : moduleHomotopyProjectiveLocus A D T.obj₁)
    (h₂ : moduleHomotopyProjectiveLocus A D T.obj₂) :
    moduleHomotopyProjectiveLocus A D T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₂.mapIso e) h₂
  exact (moduleHomotopyProjectiveLocus A D).prop_of_iso (Triangle.π₃.mapIso e.symm)
    (moduleHomotopicallyProjective_cone A D hM hN f)

instance moduleHomotopyProjectiveLocusTriangulatedClosed₃ :
    (moduleHomotopyProjectiveLocus A D).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk' (moduleHomotopyProjectiveLocus_triangle_obj₃ A D)

instance moduleHomotopyProjectiveLocusTriangulatedClosed₂ :
    (moduleHomotopyProjectiveLocus A D).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance moduleHomotopyProjectiveLocusNonempty :
    (moduleHomotopyProjectiveLocus A D).Nonempty :=
  ObjectProperty.nonempty_of_prop (X := (moduleToHomotopy A D).obj (moduleZero A D))
    (moduleHomotopicallyProjective_of_isZero A D (moduleZero_isZero A D))

instance moduleHomotopyProjectiveLocusContainsZero :
    (moduleHomotopyProjectiveLocus A D).ContainsZero := inferInstance

instance moduleHomotopyProjectiveLocusIsTriangulated :
    (moduleHomotopyProjectiveLocus A D).IsTriangulated where

variable (E : RightModule A D)

lemma endomorphismHom_thick_projective {M : ModuleCategory A D}
    (hM : endomorphismThickClosure A D E ((moduleToHomotopy A D).obj M)) :
    moduleHomotopicallyProjective A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onClosed.obj M) := by
  have hE : moduleHomotopyProjectiveLocus A (EndomorphismObject E)
      ((endomorphismModuleHom A D E).onHomotopy.obj
        ((moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) E))) :=
    moduleHomotopicallyProjective_of_iso A (EndomorphismObject E)
      (endomorphismRegularModuleIso A D E)
      (representable_homotopicallyProjective A (EndomorphismObject E) .point)
  exact dgModuleFunctor_thick_image A D (EndomorphismObject E) (endomorphismModuleHom A D E)
    E (moduleHomotopyProjectiveLocus A (EndomorphismObject E)) hE _ hM

lemma perfectEndomorphismHom_obj_projective (S : Set D) (E : PerfectDGModuleOver A D S)
    (hgen : endomorphismThickGeneratesPerfect A D S E) (M : PerfectDGModuleOver A D S) :
    moduleHomotopicallyProjective A (EndomorphismObject E.val)
      (ForgetEnrichment.of (Complex A) ((perfectEndomorphismModuleHom A D S E).obj M)) :=
  endomorphismHom_thick_projective A D E.val (hgen M)

end SerrePositivity.DifferentialGraded
