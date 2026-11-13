module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.BoundaryEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.RelativeInitialVertices

/-! # 両端を指定した普遍余錐間の辺

概要：図式間の辺は、それぞれの指定された普遍余錐間の辺へ持ち上がる。
方針：普遍余錐の全部分圏への頂点表示と一次元の相対境界充填を使う。
規約：両端を厳密に固定し、辺の図式への像も厳密に指定する。
使われ方：S4 の cofiber 列の射と suspension への接続射。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：指定された普遍余錐を普遍余錐全体の単体集合の頂点として表す。
方針：零次数の頂点条件を相対始点境界充填に移す。
規約：基底の図式を厳密に保持する。使われ方：普遍余錐間の辺の端点。 -/
def colimitCoconeVertex {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hc.initialBoundaryLifting⟩

/-- 概要：普遍余錐の頂点表示の図式への射影は元の図式の頂点表示。
方針：余錐の固定条件を使う。
規約：厳密な等式。使われ方：持ち上げる辺の端点の照合。 -/
lemma colimitCoconeVertex_projection {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) (colimitCoconeVertex c hc) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ c.val) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p
  rw [c.property]

/-- 概要：任意の図式間の辺は指定された普遍余錐間の辺へ持ち上がる。
方針：端点を射影に合わせて移送し、一次元境界の持ち上げ性を適用する。
規約：余錐の両端と、射影した辺の一次単体を厳密に固定する。
使われ方：cofiber の図式の射を余極限対象の射にする。 -/
lemma exists_colimitCocone_edge {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) :
    ∃ f : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCocones K X))
      (colimitCoconeVertex c hc) (colimitCoconeVertex d hd),
      (f.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X))).edge = e.edge := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitCoconeProjection K X
  have : HasLiftingProperty (boundary 1).ι P :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection_hasLiftingProperty_boundary (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) 0
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (P.app (Opposite.op ⦋0⦌) (colimitCoconeVertex c hc))
      (P.app (Opposite.op ⦋0⦌) (colimitCoconeVertex d hd)) := {
    edge := e.edge
    src_eq := e.src_eq.trans (colimitCoconeVertex_projection c hc).symm
    tgt_eq := e.tgt_eq.trans (colimitCoconeVertex_projection d hd).symm }
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.exists_edge_lift_of_boundary_one P
    (colimitCoconeVertex c hc) (colimitCoconeVertex d hd) e'
  exact ⟨f, congrArg SSet.Truncated.Edge.edge hf⟩

/-- 概要：図式間の辺を、指定された普遍余錐を両端とする単体的ホモトピーへ延長する。
方針：普遍余錐間の辺を関手単体集合に含めて uncurry する。
規約：元の図式のパラメーター付き写像への制限は厳密。
使われ方：cofiber 列から suspension への比較四角形の構成。 -/
lemma exists_colimitCoconeHomotopy {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex q)) :
    ∃ H : SSet.Homotopy c.val d.val,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        uncurry (SSet.yonedaEquiv.symm e.edge) := by
  obtain ⟨f, hf⟩ := exists_colimitCocone_edge c d hc hd e
  let j := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X)).ι
  let g : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val) := f.map ((truncation 2).map j)
  let s : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).obj X) _⦋1⦌ := g.edge
  let t : ((ihom K).obj X) _⦋1⦌ := e.edge
  have hs : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0])).app X).app (Opposite.op ⦋1⦌) s = t := hf
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge g, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫
    uncurry (SSet.yonedaEquiv.symm s) = uncurry (SSet.yonedaEquiv.symm t)
  rw [← uncurry_pre_app]
  congr 1
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hs

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
