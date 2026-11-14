module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGPretriangulated
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size

/-! 前三角性の明示入力から gluing の種対象を供給する。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 零加群のホモトピー表現可能性により、前三角 dg 圏は対象を持つ。 -/
lemma dgGluingPretriangulated_nonempty (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) : Nonempty C := by
  let := hC
  have h0 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C
      ((moduleToHomotopy R C).obj (moduleZero R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C).prop_of_isZero
      ((moduleToHomotopy R C).map_isZero (moduleZero_isZero R C))
  obtain ⟨x, _⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C _).1 h0
  exact ⟨x⟩

variable (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 両成分を指定し、比較閉元を零に取った実 gluing 対象。 -/
def dgGluingSeedObject (c : C) (d : D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M where
  left := c
  right := d
  gluing := 0

/-- 元の両圏の前三角性から、余分な非空性の仮定なしに gluing の対象を得る。 -/
lemma dgGluing_nonempty (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  ⟨dgGluingSeedObject R C D M (Classical.choice (dgGluingPretriangulated_nonempty R C hC))
    (Classical.choice (dgGluingPretriangulated_nonempty R D hD))⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
