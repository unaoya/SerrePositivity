module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiniteCellVertexClosure
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberLocalizingBaseChange

/-! # 有限 cell の cone による実加群分母の判定

概要：閉加群射の実 cofiber 分母条件は、K(D) の指定有限 cell の trW と一致する。
方針：標準実 cone と任意の cofiber の選択独立性、生成条件の一致を使う。
規約：retract は加えず元の Hom の平坦性も要求しない。使われ方：有限 cell roof の実辺化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 実加群射が指定 cofiber 分母であることは、標準 cone の有限 cell 条件と同値。 -/
theorem dgModule_cofiberEdges_iff_finiteCell (S : Set D)
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D S) x} ↔
      _root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D S
        ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).obj (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) := by
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D S)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberSquare A D f)
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberSquare A D f).cofiber =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_vertex11 A D f
  rw [hc] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModule_stableVertexClosure_iff_finiteCell A D S _)

/-- 実加群辺の分母条件は、同じ閉射の K(D) での三角的分母条件と同値。 -/
theorem dgModule_cofiberEdges_iff_trW (S : Set D)
    {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleGeneratorVertices A D S) x} ↔
      (_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D S).trW ((_root_.SerrePositivity.DifferentialGraded.moduleToHomotopy A D).map f) := by
  exact (dgModule_cofiberEdges_iff_finiteCell A D S f).trans
    ((_root_.SerrePositivity.DifferentialGraded.homotopyFiniteCellOver A D S).trW_iff_of_distinguished
      (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyConeTriangle A D f)
      (_root_.SerrePositivity.DifferentialGraded.moduleHomotopyConeTriangle_distinguished A D f)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
