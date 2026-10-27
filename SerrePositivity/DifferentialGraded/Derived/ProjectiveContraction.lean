module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopy

/-! # ホモトピー射影的かつ非輪状な加群の明示的収縮

全次数 Hom end の非輪状性により、恒等の次数 −1 の原像を取る。
収縮は全 dg 作用と自然であり、対象別の収縮の選択を並べるものではない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- ホモトピー射影的かつ対象ごと非輪状な加群の恒等は、実 Hom end の境界である。 -/
theorem moduleHomotopicallyProjective_contractingElement_of_acyclic
    (M : RightModule R D)
    (hM : moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) M))
    (hA : moduleAcyclic R D (ForgetEnrichment.of (Complex R) M)) :
    ∃ H : GradedHom R M M (-1),
      (homObject R (RightModule R D) M M).d (-1) 0 H = (unitElement R M).val := by
  exact complexAcyclic_boundary (hM _ hA) 0 (unitElement R M).val (differential_unit R M)

end SerrePositivity.DifferentialGraded
