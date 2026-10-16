module
public import SerrePositivity.DifferentialGraded.Perfect.FiniteCell
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveFiniteOperations
public import SerrePositivity.DifferentialGraded.Tensor.ProjectiveKFlat

/-! # 有限cellの全Hom射影性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 有限操作の構成木から、全Hom endによる射影性を帰納的に得る。 -/
lemma ModuleFiniteCellCode.homotopicallyProjective {S : Set D} {M : ModuleCategory A D}
    (c : ModuleFiniteCellCode A D S M) : moduleHomotopicallyProjective A D M := by
  induction c with
  | zero => exact moduleHomotopicallyProjective_of_isZero A D (moduleZero_isZero A D)
  | generator x hx => exact representable_homotopicallyProjective A D x
  | shift s c ih => exact moduleHomotopicallyProjective_shift A D ih s
  | sum c d ihc ihd => exact moduleHomotopicallyProjective_biprod A D ihc ihd
  | cone c d f ihc ihd => exact moduleHomotopicallyProjective_cone A D ihc ihd f
  | iso c e ih => exact moduleHomotopicallyProjective_of_iso A D e ih

lemma moduleFiniteCellOver_homotopicallyProjective {S : Set D} {M : ModuleCategory A D}
    (hM : moduleFiniteCellOver A D S M) : moduleHomotopicallyProjective A D M := by
  obtain ⟨c⟩ := hM
  exact c.homotopicallyProjective A D

lemma moduleFiniteCell_homotopicallyProjective {M : ModuleCategory A D}
    (hM : moduleFiniteCell A D M) : moduleHomotopicallyProjective A D M :=
  moduleFiniteCellOver_homotopicallyProjective A D hM

/-- finite cellはHom_DのA-flat性なしに相対K-flatでもある。 -/
lemma moduleFiniteCell_relativeKFlat {M : ModuleCategory A D}
    (hM : moduleFiniteCell A D M) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M) :=
  moduleHomotopicallyProjective_relativeKFlat A D (moduleFiniteCell_homotopicallyProjective A D hM)

end SerrePositivity.DifferentialGraded
