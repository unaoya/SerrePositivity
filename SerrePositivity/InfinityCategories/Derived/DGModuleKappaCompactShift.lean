module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSuspensionComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalenceUniverse
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ閉加群同型で実導来 κ-compact 性を輸送する。 -/
lemma dgModuleKappaCompact_iff_of_iso {κ : Cardinal.{u}}
    {M N : ModuleCategory R D} (e : M ≅ N) :
    dgModuleKappaCompact R D κ M ↔ dgModuleKappaCompact R D κ N :=
  dgModuleKappaCompact_iff_of_derivedIso R D ((moduleToDerived R D).mapIso e)

/-- 同じ実加群の一回 shift と元の加群の κ-compact 性は同値。 -/
lemma dgModuleKappaCompact_shift_one_iff {κ : Cardinal.{u}} (M : ModuleCategory R D) :
    dgModuleKappaCompact R D κ (M⟦(1 : ℤ)⟧) ↔ dgModuleKappaCompact R D κ M := by
  let X := dgModuleDerivedInfinityCategory R D
  let := dgModuleDerivedInfinityCategory_isStable R D
  let e := suspensionQCatEquivalence X
  let x := dgConeModuleDerivedVertex R D M
  have h := F2.Presentable.isKappaCompact_iff_equivalence_universe.{u, max (u + 1) v}
    (κ := κ) e x
  have i : VertexIso (e.hom.app _ x) (dgConeModuleDerivedVertex R D (M⟦(1 : ℤ)⟧)) := by
    change (suspensionQCatEquivalence X).toHoEquivalence.functor.obj
      (SSet.HomotopyCategory.mk x) ≅ _
    rw [suspensionQCatEquivalence_ho_functor]
    exact dgConeModuleDerivedShiftOneSuspensionIso R D M
  exact (h.trans (F2.Compact.isKappaCompact_iff_of_iso.{u, max (u + 1) v} i)).symm

/-- 全ての整数 shift は、同じ加群の実導来 κ-compact 性を保つ。 -/
lemma dgModuleKappaCompact_shift {κ : Cardinal.{u}} {M : ModuleCategory R D}
    (hM : dgModuleKappaCompact R D κ M) (s : ℤ) :
    dgModuleKappaCompact R D κ (M⟦s⟧) := by
  let C := ModuleCategory R D
  have hpos (N : C) : dgModuleKappaCompact R D κ N →
      dgModuleKappaCompact R D κ (N⟦(1 : ℤ)⟧) :=
    (dgModuleKappaCompact_shift_one_iff R D N).mpr
  have hneg (N : C) (hN : dgModuleKappaCompact R D κ N) :
      dgModuleKappaCompact R D κ (N⟦(-1 : ℤ)⟧) := by
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
lemma dgModuleKappaCompact_shift_iff {κ : Cardinal.{u}} (M : ModuleCategory R D) (s : ℤ) :
    dgModuleKappaCompact R D κ (M⟦s⟧) ↔ dgModuleKappaCompact R D κ M := by
  constructor
  · intro h
    exact (dgModuleKappaCompact_iff_of_iso R D
      (((shiftFunctorAdd' (ModuleCategory R D) s (-s) 0 (by omega)).app M).symm ≪≫
        (shiftFunctorZero (ModuleCategory R D) ℤ).app M)).mp
          (dgModuleKappaCompact_shift R D h (-s))
  · exact fun h ↦ dgModuleKappaCompact_shift R D h s

end SerrePositivity.InfinityCategories
