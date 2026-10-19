module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiniteCellVertexClosure
public import SerrePositivity.InfinityCategories.Stable.CofiberLocalizingBaseChange

/-! # 有限 cell の cone による実加群分母の判定

概要：閉加群射の実 cofiber 分母条件は、K(D) の指定有限 cell の trW と一致する。
方針：標準実 cone と任意の cofiber の選択独立性、生成条件の一致を使う。
規約：retract は加えず元の Hom の平坦性も要求しない。使われ方：有限 cell roof の実辺化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実加群射が指定 cofiber 分母であることは、標準 cone の有限 cell 条件と同値。 -/
theorem dgModule_cofiberEdges_iff_finiteCell (S : Set D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgModuleEdge A D f).edge ∈ cofiberLocalizingEdges
      {x | StableVertexClosure (dgModuleGeneratorVertices A D S) x} ↔
      homotopyFiniteCellOver A D S
        ((moduleToHomotopy A D).obj (moduleCone A D f)) := by
  have h := cofiberStableEdges_edge_mem_iff (dgModuleGeneratorVertices A D S)
    (dgModuleCofiberSquare A D f)
  have hc : (dgModuleCofiberSquare A D f).cofiber =
      Simplex.vertex (ForgetEnrichment.to (Complex A) (moduleCone A D f)) :=
    dgModuleConeSquare_vertex11 A D f
  rw [hc] at h
  exact h.trans (dgModule_stableVertexClosure_iff_finiteCell A D S _)

/-- 実加群辺の分母条件は、同じ閉射の K(D) での三角的分母条件と同値。 -/
theorem dgModule_cofiberEdges_iff_trW (S : Set D)
    {M N : ModuleCategory A D} (f : M ⟶ N) :
    (dgModuleEdge A D f).edge ∈ cofiberLocalizingEdges
      {x | StableVertexClosure (dgModuleGeneratorVertices A D S) x} ↔
      (homotopyFiniteCellOver A D S).trW ((moduleToHomotopy A D).map f) := by
  exact (dgModule_cofiberEdges_iff_finiteCell A D S f).trans
    ((homotopyFiniteCellOver A D S).trW_iff_of_distinguished
      (moduleHomotopyConeTriangle A D f)
      (moduleHomotopyConeTriangle_distinguished A D f)).symm

end SerrePositivity.InfinityCategories
