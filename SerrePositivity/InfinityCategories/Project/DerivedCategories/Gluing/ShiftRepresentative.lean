module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulated

/-! 元の前三角 dg 圏の任意整数シフトの代表を、同じ加群の K(D) 同型として選ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (x : D) (n : ℤ)

/-- 元の同じ代表加群の整数シフトを表す実対象と、全加群のホモトピー圏の同型。 -/
structure DGGluingShiftRepresentative where
  obj : D
  comparison :
    (moduleToHomotopy R D).obj
      ((ForgetEnrichment.of (Complex R) (representable R x))⟦n⟧) ≅
    (moduleToHomotopy R D).obj (ForgetEnrichment.of (Complex R) (representable R obj))

/-- 元の前三角性から、負の整数も含めて同じシフト加群の代表が存在。 -/
lemma dgGluingShiftRepresentative_nonempty (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    Nonempty (DGGluingShiftRepresentative R D x n) := by
  let := hD
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty_shift R D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R D)
    (ForgetEnrichment.of (Complex R) (representable R x)) n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable_representable R D x)
  obtain ⟨y, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R D _).1 hs
  exact ⟨⟨y, e⟩⟩

/-- 明示された元の前三角性から選ぶ、同じ任意整数シフトの代表。 -/
def dgGluingChooseShiftRepresentative (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    DGGluingShiftRepresentative R D x n :=
  Classical.choice (dgGluingShiftRepresentative_nonempty R D x n hD)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
