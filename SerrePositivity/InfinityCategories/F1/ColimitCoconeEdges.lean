module
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.BoundaryEdgeLifting
public import SerrePositivity.InfinityCategories.Core.CoconeFamily
public import SerrePositivity.InfinityCategories.F1.ColimitCoconeFamilies
public import SerrePositivity.InfinityCategories.F1.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Core.RelativeInitialVertices

/-! # 両端を指定した普遍余錐間の辺

概要：図式間の辺は、それぞれの指定された普遍余錐間の辺へ持ち上がる。
方針：普遍余錐の全部分圏への頂点表示と一次元の相対境界充填を使う。
規約：両端を厳密に固定し、辺の図式への像も厳密に指定する。
使われ方：S4 の cofiber 列の射と suspension への接続射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定された普遍余錐を普遍余錐全体の単体集合の頂点として表す。
方針：零次数の頂点条件を相対始点境界充填に移す。
規約：基底の図式を厳密に保持する。使われ方：普遍余錐間の辺の端点。 -/
def colimitCoconeVertex {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) : (colimitCocones K X) _⦋0⦌ :=
  ⟨functorVertex c.val, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    exact hc.initialBoundaryLifting⟩

/-- 概要：普遍余錐の頂点表示の図式への射影は元の図式の頂点表示。
方針：余錐の固定条件を使う。
規約：厳密な等式。使われ方：持ち上げる辺の端点の照合。 -/
lemma colimitCoconeVertex_projection {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    (colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) (colimitCoconeVertex c hc) =
      functorVertex p := by
  change functorVertex (joinInl K Δ[0] ≫ c.val) = functorVertex p
  rw [c.property]

/-- 概要：任意の図式間の辺は指定された普遍余錐間の辺へ持ち上がる。
方針：端点を射影に合わせて移送し、一次元境界の持ち上げ性を適用する。
規約：余錐の両端と、射影した辺の一次単体を厳密に固定する。
使われ方：cofiber の図式の射を余極限対象の射にする。 -/
lemma exists_colimitCocone_edge {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (functorVertex p) (functorVertex q)) :
    ∃ f : SSet.Truncated.Edge (X := (truncation 2).obj (colimitCocones K X))
      (colimitCoconeVertex c hc) (colimitCoconeVertex d hd),
      (f.map ((truncation 2).map (colimitCoconeProjection K X))).edge = e.edge := by
  let P := colimitCoconeProjection K X
  have : HasLiftingProperty (boundary 1).ι P :=
    relativeInitialProjection_hasLiftingProperty_boundary (coconeRestriction K X) 0
  let e' : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (P.app (Opposite.op ⦋0⦌) (colimitCoconeVertex c hc))
      (P.app (Opposite.op ⦋0⦌) (colimitCoconeVertex d hd)) := {
    edge := e.edge
    src_eq := e.src_eq.trans (colimitCoconeVertex_projection c hc).symm
    tgt_eq := e.tgt_eq.trans (colimitCoconeVertex_projection d hd).symm }
  obtain ⟨f, hf⟩ := exists_edge_lift_of_boundary_one P
    (colimitCoconeVertex c hc) (colimitCoconeVertex d hd) e'
  exact ⟨f, congrArg SSet.Truncated.Edge.edge hf⟩

/-- 概要：図式間の辺を、指定された普遍余錐を両端とする単体的ホモトピーへ延長する。
方針：普遍余錐間の辺を関手単体集合に含めて uncurry する。
規約：元の図式のパラメーター付き写像への制限は厳密。
使われ方：cofiber 列から suspension への比較四角形の構成。 -/
lemma exists_colimitCoconeHomotopy {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (c : JoinCocone p) (d : JoinCocone q) (hc : IsColimitCone c) (hd : IsColimitCone d)
    (e : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (functorVertex p) (functorVertex q)) :
    ∃ H : SSet.Homotopy c.val d.val,
      (joinInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        uncurry (SSet.yonedaEquiv.symm e.edge) := by
  obtain ⟨f, hf⟩ := exists_colimitCocone_edge c d hc hd e
  let j := (relativeInitialVertices (coconeRestriction K X)).ι
  let g : SSet.Truncated.Edge
      (X := (truncation 2).obj ((ihom (join K (Δ[0] : SSet.{u}))).obj X))
      (functorVertex c.val) (functorVertex d.val) := f.map ((truncation 2).map j)
  let s : ((ihom (join K (Δ[0] : SSet.{u}))).obj X) _⦋1⦌ := g.edge
  let t : ((ihom K).obj X) _⦋1⦌ := e.edge
  have hs : ((pre (joinInl K Δ[0])).app X).app (Opposite.op ⦋1⦌) s = t := hf
  refine ⟨simplicialHomotopyOfFunctorEdge g, ?_⟩
  change (joinInl K Δ[0] ▷ (Δ[1] : SSet.{u})) ≫
    uncurry (SSet.yonedaEquiv.symm s) = uncurry (SSet.yonedaEquiv.symm t)
  rw [← uncurry_pre_app]
  congr 1
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hs

end SerrePositivity.InfinityCategories
