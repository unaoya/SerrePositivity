module
public import SerrePositivity.DifferentialGraded.Perfect.CompactTriangles
public import SerrePositivity.DifferentialGraded.Perfect.Triangulated

/-! # 有限cellとそのretractのcompact性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleCompact_derivedShift {M : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M)) (n : ℤ) :
    moduleCompact A D ((moduleToDerived A D).obj (M⟦n⟧)) :=
  (moduleCompact A D).prop_of_iso (((moduleToDerived A D).commShiftIso n).app M).symm
    (moduleCompact_shift A D hM n)

lemma moduleCompact_derivedBiprod {M N : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M))
    (hN : moduleCompact A D ((moduleToDerived A D).obj N)) :
    moduleCompact A D ((moduleToDerived A D).obj (moduleBiprod A D M N)) := by
  rw [moduleCompact_iff_comparison_surjective]
  intro J F f
  have ht := congrArg ((moduleToDerived A D).map) (moduleBinaryBicone_total A D M N)
  change (moduleToDerived A D).map
    (moduleBiprodFst A D M N ≫ moduleBiprodInl A D M N +
      moduleBiprodSnd A D M N ≫ moduleBiprodInr A D M N) =
    (moduleToDerived A D).map (𝟙 (moduleBiprod A D M N)) at ht
  simp only [Functor.map_add, Functor.map_comp] at ht
  rw [(moduleToDerived A D).map_id] at ht
  have hf : f =
      (moduleToDerived A D).map (moduleBiprodFst A D M N) ≫
        ((moduleToDerived A D).map (moduleBiprodInl A D M N) ≫ f) +
      (moduleToDerived A D).map (moduleBiprodSnd A D M N) ≫
        ((moduleToDerived A D).map (moduleBiprodInr A D M N) ≫ f) := by
    rw [← Category.assoc, ← Category.assoc, ← Preadditive.add_comp, ht, Category.id_comp]
  change f ∈ (moduleCompactComparison A D _ F).range
  rw [hf]
  exact Submodule.add_mem _
    (moduleCompactRange_precompose A D hM F _ _)
    (moduleCompactRange_precompose A D hN F _ _)

lemma moduleCompact_derivedCone {M N : ModuleCategory A D}
    (hM : moduleCompact A D ((moduleToDerived A D).obj M))
    (hN : moduleCompact A D ((moduleToDerived A D).obj N)) (f : M ⟶ N) :
    moduleCompact A D ((moduleToDerived A D).obj (moduleCone A D f)) :=
  moduleCompact_triangle_obj₃ A D (moduleDerivedConeTriangle A D f)
    (moduleDerivedConeTriangle_distinguished A D f) hM hN

lemma ModuleFiniteCellCode.compact {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) : moduleCompact A D ((moduleToDerived A D).obj M) := by
  induction c with
  | zero =>
    exact moduleCompact_of_isZero A D
      ((moduleToDerived A D).map_isZero (moduleZero_isZero A D))
  | generator x hx => exact moduleRepresentable_compact A D x
  | shift s c ih => exact moduleCompact_derivedShift A D ih s
  | sum c d ihc ihd => exact moduleCompact_derivedBiprod A D ihc ihd
  | cone c d f ihc ihd => exact moduleCompact_derivedCone A D ihc ihd f
  | iso c e ih => exact (moduleCompact A D).prop_of_iso ((moduleToDerived A D).mapIso e) ih

lemma moduleFiniteCellOver_compact {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleCompact A D ((moduleToDerived A D).obj M) := by
  obtain ⟨c⟩ := hM
  exact c.compact A D

lemma moduleFiniteCell_compact {M : ModuleCategory A D} (hM : moduleFiniteCell A D M) :
    moduleCompact A D ((moduleToDerived A D).obj M) := moduleFiniteCellOver_compact A D hM

lemma modulePerfectOver_compact {S : Set D} {X : DerivedModuleCategory A D}
    (hX : modulePerfectOver A D S X) : moduleCompact A D X := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfectOver_iff A D S X).mp hX
  exact moduleCompact_of_retract A D r (moduleFiniteCellOver_compact A D hM)

lemma modulePerfect_compact {X : DerivedModuleCategory A D} (hX : modulePerfect A D X) :
    moduleCompact A D X := modulePerfectOver_compact A D hX

end SerrePositivity.DifferentialGraded
