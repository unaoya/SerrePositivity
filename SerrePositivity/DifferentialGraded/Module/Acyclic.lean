module
public import SerrePositivity.DifferentialGraded.Complexes.AcyclicCone
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Module.HomotopyQuasiIso

/-! # objectwise acyclic な加群と cone による準同型の判定 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- すべての対象で評価複体が acyclic な加群。 -/
def moduleAcyclic : ObjectProperty (ModuleCategory A D) :=
  fun M => ∀ x : D, ((moduleEvaluation A D x).obj M).Acyclic

lemma moduleAcyclic_iff (M : ModuleCategory A D) :
    moduleAcyclic A D M ↔ ∀ (x : D) (i : ℤ),
      ((moduleEvaluation A D x).obj M).ExactAt i := Iff.rfl

/-- K(D) 上の acyclic 性を、既存の複体ホモトピー圏の評価で判定する。 -/
def moduleHomotopyAcyclic : ObjectProperty (ModuleHomotopyCategory A D) :=
  fun M => ∀ x : D, _root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)
    ((moduleHomotopyEvaluation A D x).obj M)

/-- 商関手は objectwise acyclic 性を保ち、反映する。 -/
lemma moduleHomotopyAcyclic_obj_iff (M : ModuleCategory A D) :
    moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj M) ↔ moduleAcyclic A D M := by
  change (∀ x : D, _root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)
    ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj
      ((moduleEvaluation A D x).obj M))) ↔ _
  simp only [_root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic,
    moduleAcyclic]

lemma moduleHomotopyAcyclic_iff (M : ModuleHomotopyCategory A D) :
    moduleHomotopyAcyclic A D M ↔ ∀ (x : D) (i : ℤ),
      IsZero ((moduleHomotopyHomology A D x i).obj M) := by
  simp only [moduleHomotopyAcyclic, _root_.HomotopyCategory.mem_subcategoryAcyclic_iff]
  rfl

/-- 加群射の準同型性は、全 dg 作用を持つ標準 cone の objectwise acyclic 性と同値。 -/
lemma moduleQuasiIso_iff_acyclic_cone {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D f ↔ moduleAcyclic A D (moduleCone A D f) := by
  change (∀ x : D, QuasiIso ((moduleEvaluation A D x).map f)) ↔
    ∀ x : D, (mappingCone ((moduleEvaluation A D x).map f)).Acyclic
  exact forall_congr' (fun x => complex_quasiIso_iff_acyclic_cone A _)

/-- K(D) の準同型判定にも同じ加群 cone を使用できる。 -/
lemma moduleHomotopyQuasiIso_iff_acyclic_cone {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
      moduleHomotopyAcyclic A D ((moduleToHomotopy A D).obj (moduleCone A D f)) := by
  rw [moduleHomotopyQuasiIso_map_iff, moduleHomotopyAcyclic_obj_iff,
    moduleQuasiIso_iff_acyclic_cone]

end SerrePositivity.DifferentialGraded
