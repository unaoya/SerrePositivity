module
public import SerrePositivity.DifferentialGraded.Module.ShiftHom
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.HomotopyQuasiIso
public import Mathlib.CategoryTheory.Shift.Quotient
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # K(D) の整数 shift と quasiIso の保存 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance moduleBoundaryCompatibleWithShift :
    (boundaryRelation A (RightModule A D)).IsCompatibleWithShift ℤ where
  condition s M N f g h := by
    have hs := (moduleShiftDG A D s).preserves_boundary f g h
    change boundaryRelation A (RightModule A D)
      ((moduleShiftFunctor A D s).map f) ((moduleShiftFunctor A D s).map g)
    rw [← moduleShiftDG_onClosed_eq]
    exact hs

/-- 全 dg 自然な加群ホモトピーはすべての整数 shift で保存される。 -/
lemma moduleHomotopy_shift {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (s : ℤ) :
    Nonempty (ModuleHomotopy A D (f⟦s⟧') (g⟦s⟧')) := by
  apply (moduleHomotopy_nonempty_iff A D _ _).2
  exact HomRel.IsCompatibleWithShift.condition s f g
    ((moduleHomotopy_nonempty_iff A D f g).1 ⟨h⟩)

-- Mathlib の商 shift は元の zero/add coherence を運ぶ。
instance moduleHomotopyEvaluationCommShift (x : D) :
    (moduleHomotopyEvaluation A D x).CommShift ℤ := by
  unfold moduleHomotopyEvaluation
  infer_instance

/-- 閉零加群の準同型判定は整数 shift で不変。 -/
lemma moduleQuasiIso_shift_iff {M N : ModuleCategory A D} (f : M ⟶ N) (s : ℤ) :
    moduleQuasiIso A D (f⟦s⟧') ↔ moduleQuasiIso A D f := by
  simp only [moduleQuasiIso_iff]
  apply forall_congr'
  intro x
  change QuasiIso ((moduleEvaluation A D x).map (moduleShiftMap A D s f)) ↔ _
  rw [moduleShiftMap_eval]
  exact CochainComplex.quasiIso_shift_iff _ s

instance moduleQuasiIsoCompatibleWithShift : (moduleQuasiIso A D).IsCompatibleWithShift ℤ where
  condition s := by
    ext M N f
    exact moduleQuasiIso_shift_iff A D f s

/-- K(D) の準同型判定も整数 shift で不変。評価の CommShift を使用する。 -/
lemma moduleHomotopyQuasiIso_shift_iff {M N : ModuleHomotopyCategory A D}
    (f : M ⟶ N) (s : ℤ) :
    moduleHomotopyQuasiIso A D (f⟦s⟧') ↔ moduleHomotopyQuasiIso A D f := by
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map (f⟦s⟧'))) ↔ _
  apply forall_congr'
  intro x
  let W := _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
  let E := moduleHomotopyEvaluation A D x
  have hi := W.arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (E.commShiftIso s)).app (Arrow.mk f))
  change W (E.map (f⟦s⟧')) ↔ W ((E.map f)⟦s⟧') at hi
  exact hi.trans (MorphismProperty.IsCompatibleWithShift.iff W (E.map f) s)

instance moduleHomotopyQuasiIsoCompatibleWithShift :
    (moduleHomotopyQuasiIso A D).IsCompatibleWithShift ℤ where
  condition s := by
    ext M N f
    exact moduleHomotopyQuasiIso_shift_iff A D f s

end SerrePositivity.DifferentialGraded
