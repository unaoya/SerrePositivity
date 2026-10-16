module
public import SerrePositivity.DifferentialGraded.Perfect.Triangulated
public import SerrePositivity.DifferentialGraded.Derived.Linear
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Perfは指定代表加群を含む最小の厚い部分圏 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]

lemma moduleDerivedBiprod_mem_triangulated {M N : ModuleCategory A D}
    (hM : P ((moduleToDerived A D).obj M)) (hN : P ((moduleToDerived A D).obj N)) :
    P ((moduleToDerived A D).obj (moduleBiprod A D M N)) := by
  have : PreservesBinaryBiproducts (moduleToDerived A D) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have h := P.ext_of_isTriangulatedClosed₂'
    (binaryBiproductTriangle ((moduleToDerived A D).obj M) ((moduleToDerived A D).obj N))
    (binaryBiproductTriangle_distinguished _ _) hM hN
  rw [ObjectProperty.isoClosure_eq_self] at h
  exact P.prop_of_iso
    ((moduleToDerived A D).mapIso (moduleBiprodIso A D M N) ≪≫
      (moduleToDerived A D).mapBiprod M N).symm h

lemma ModuleFiniteCellCode.mem_triangulated {S : Set D}
    (hgen : ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))))
    {M : ModuleCategory A D} (c : ModuleFiniteCellCode A D S M) :
    P ((moduleToDerived A D).obj M) := by
  induction c with
  | zero => exact P.prop_of_isZero ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))
  | generator x hx => exact hgen x hx
  | @shift M s c ih =>
    exact P.prop_of_iso (((moduleToDerived A D).commShiftIso s).app M).symm
      (P.le_shift s _ ih)
  | sum c d ihc ihd => exact moduleDerivedBiprod_mem_triangulated A D P ihc ihd
  | cone c d f ihc ihd =>
    have h := P.ext_of_isTriangulatedClosed₃' (moduleDerivedConeTriangle A D f)
      (moduleDerivedConeTriangle_distinguished A D f) ihc ihd
    rw [ObjectProperty.isoClosure_eq_self] at h
    exact h
  | iso c e ih => exact P.prop_of_iso ((moduleToDerived A D).mapIso e) ih

lemma derivedFiniteCellOver_le_iff_generators (S : Set D) :
    derivedFiniteCellOver A D S ≤ P ↔ ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · intro h x hx
    exact h _ ((moduleFiniteCellOver A D S).prop_map_obj (moduleToDerived A D)
      (moduleFiniteCellOver_representable A D x hx))
  · intro h X hX
    obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := hX
    exact P.prop_of_iso e (c.mem_triangulated A D P h)

lemma modulePerfectOver_le_of_generators [P.IsStableUnderRetracts] (S : Set D)
    (hgen : ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))) :
    modulePerfectOver A D S ≤ P := by
  rw [modulePerfectOver_le_iff]
  intro M hM
  obtain ⟨c⟩ := hM
  exact c.mem_triangulated A D P hgen

lemma modulePerfectOver_le_iff_generators [P.IsStableUnderRetracts] (S : Set D) :
    modulePerfectOver A D S ≤ P ↔ ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  constructor
  · intro h x hx
    exact h _ (modulePerfectOver_representable A D x hx)
  · exact modulePerfectOver_le_of_generators A D P S

lemma modulePerfect_le_iff_generators [P.IsStableUnderRetracts] :
    modulePerfect A D ≤ P ↔ ∀ x : D, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x))) := by
  change modulePerfectOver A D Set.univ ≤ P ↔ _
  rw [modulePerfectOver_le_iff_generators]
  simp only [Set.mem_univ, forall_const]

end SerrePositivity.DifferentialGraded
