module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSuspensionComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactEquivalenceUniverse
/-!
概要：実加群の全整数 shift は、元の全 Hom による κ-compact 性を保ち反映する。
方針：一回 shift を native 懸垂自己同値で扱い、同じ実加群の shift 合成同型で整数帰納する。
規約：κ と試験添字の宇宙を固定し、ordinary compact や追加の交換入力を使わない。
使われ方：D-8 c3 の shift 入力、sphere-free 基底と perfect 代表の全シフト。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- 同じ閉加群同型で実導来 κ-compact 性を輸送する。 -/
lemma dgModuleKappaCompact_iff_of_iso {κ : Cardinal.{u}}
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D} (e : M ≅ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact_iff_of_derivedIso R D ((moduleToDerived R D).mapIso e)

/-- 同じ実加群の一回 shift と元の加群の κ-compact 性は同値。 -/
lemma dgModuleKappaCompact_shift_one_iff {κ : Cardinal.{u}} (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M⟦(1 : ℤ)⟧) ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M := by
  let X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory_isStable R D
  let e := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X
  let x := dgConeModuleDerivedVertex R D M
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_iff_equivalence_universe.{u, max (u + 1) v}
    (κ := κ) e x
  have i : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (e.hom.app _ x) (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) := by
    change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence X).toHoEquivalence.functor.obj
      (SSet.HomotopyCategory.mk x) ≅ _
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionQCatEquivalence_ho_functor]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgConeModuleDerivedShiftOneSuspensionIso R D M
  exact (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso.{u, max (u + 1) v} i)).symm

/-- 全ての整数 shift は、同じ加群の実導来 κ-compact 性を保つ。 -/
lemma dgModuleKappaCompact_shift {κ : Cardinal.{u}} {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (hM : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M⟦s⟧) := by
  let C := _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D
  have hpos (N : C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N →
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (N⟦(1 : ℤ)⟧) :=
    (dgModuleKappaCompact_shift_one_iff R D N).mpr
  have hneg (N : C) (hN : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ N) :
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (N⟦(-1 : ℤ)⟧) := by
    apply (dgModuleKappaCompact_shift_one_iff R D (N⟦(-1 : ℤ)⟧)).mp
    exact (dgModuleKappaCompact_iff_of_iso R D
      (((shiftFunctorAdd' C (-1) 1 0 (by omega)).app N).symm ≪≫
        (shiftFunctorZero C ℤ).app N)).mpr hN
  induction s using Int.induction_on with
  | zero => exact (dgModuleKappaCompact_iff_of_iso R D
      ((shiftFunctorZero C ℤ).app M)).mpr hM
  | succ n ih => exact (dgModuleKappaCompact_iff_of_iso R D
      ((shiftFunctorAdd C (n : ℤ) 1).app M)).mpr (hpos _ ih)
  | pred n ih => exact (dgModuleKappaCompact_iff_of_iso R D
      ((shiftFunctorAdd' C (-(n : ℤ)) (-1) (-(n : ℤ) - 1) (by omega)).app M)).mpr (hneg _ ih)

/-- 全整数 shift に関する、元の全共変 Hom の κ-compact 性の必要十分条件。 -/
lemma dgModuleKappaCompact_shift_iff {κ : Cardinal.{u}} (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ (M⟦s⟧) ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleKappaCompact R D κ M := by
  constructor
  · intro h
    exact (dgModuleKappaCompact_iff_of_iso R D
      (((shiftFunctorAdd' (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) s (-s) 0 (by omega)).app M).symm ≪≫
        (shiftFunctorZero (_root_.SerrePositivity.DifferentialGraded.ModuleCategory R D) ℤ).app M)).mp
          (dgModuleKappaCompact_shift R D h (-s))
  · exact fun h ↦ dgModuleKappaCompact_shift R D h s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
