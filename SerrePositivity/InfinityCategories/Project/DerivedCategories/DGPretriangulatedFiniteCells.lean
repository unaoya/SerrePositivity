module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGHomotopyFiniteCellGeneration

/-! # 前三角性と有限 cell の表現可能性

概要：dg 前三角性は K(D) の全有限 cell がホモトピー表現可能であることと同値。
方針：生成性と、代表加群が有限 cell であることから二つの対象条件を同定する。
規約：retract 閉性や完備化は要求しない。使われ方：平坦商の前三角性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- ホモトピー表現可能な加群は有限 cell の K(D) の本質像に入る。 -/
lemma dgRepresentableHomotopyProperty_le_finiteCell :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D ≤ homotopyFiniteCellOver A D Set.univ := by
  intro M hM
  obtain ⟨x, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff A D M).1 hM
  exact (homotopyFiniteCellOver A D Set.univ).prop_of_iso e.symm
    ((moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D x))

/-- 前三角 dg 圏では有限 cell の本質像はホモトピー表現可能部分と等しい。 -/
lemma dgRepresentableHomotopyProperty_eq_finiteCell [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D = homotopyFiniteCellOver A D Set.univ := by
  apply le_antisymm (dgRepresentableHomotopyProperty_le_finiteCell A D)
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.homotopyFiniteCellOver_le_iff_generators A D
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D) Set.univ).2
  intro x _
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_representable A D x

/-- 全有限 cell のホモトピー表現可能性は dg 前三角性を特徴付ける。 -/
lemma isDGPretriangulated_iff_finiteCell_representable :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D ↔
      homotopyFiniteCellOver A D Set.univ ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D := by
  constructor
  · intro h
    let := h
    rw [dgRepresentableHomotopyProperty_eq_finiteCell A D]
  · intro h
    have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D = homotopyFiniteCellOver A D Set.univ :=
      le_antisymm (dgRepresentableHomotopyProperty_le_finiteCell A D) h
    change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D).IsTriangulated
    rw [he]
    infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
