module
public import SerrePositivity.KST.SConstruction.KanSpanTriangleLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramHomotopy

/-! # 境界の逆・合成三角形を保持する全パラメータ族
概要：Kan 写像空間内の二つの辺の族を、指定した境界の逆・合成の証人を保って合成する。
方針：全パラメータを関手空間の辺とし、境界への制限 fibration に沿って持ち上げる。
規約：頂点ごとの独立な逆は選ばず、境界の二辺と二単体を全次数で厳密に回収する。
使われ方：prism の復号の全パラメータ族を相対厳密化へ渡す際の整合的な選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全パラメータの span の逆・合成を、境界の指定二単体を保持して持ち上げる。 -/
def relativeKanSpanFamilyData {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {z x y : ((ihom U).obj E) _⦋0⦌}
    (a : ((ihom U).obj E).Edge z x) (b : ((ihom U).obj E).Edge z y)
    (t : KanSpanTriangleData (a.map ((pre j).app E)) (b.map ((pre j).app E))) :
    KanSpanTriangleDataOver ((pre j).app E) a b t := by
  let : Fibration ((pre j).app E) := inferInstance
  exact kanSpanTriangleDataLift ((pre j).app E) a b t

/-- 元の二つの円柱の全パラメータを保持し、指定境界の span の証人へ厳密に戻る合成。 -/
def relativeKanHomotopySpanData {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))) :=
  relativeKanSpanFamilyData j (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)) t

/-- 構成した全パラメータの実合成ホモトピー。 -/
def relativeKanHomotopySpanComposite {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))) :
    SSet.Homotopy F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (relativeKanHomotopySpanData j a b t).data.edge.toTruncated

/-- 境界に指定した元の合成辺を、そのまま実ホモトピーへ展開したもの。 -/
def relativeKanHomotopySpanBoundary {T U E : SSet.{u}}
    (j : T ⟶ U) {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))) :
    SSet.Homotopy (j ≫ F) (j ≫ G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge t.edge.toTruncated

/-- 全パラメータの合成円柱は、境界で指定した元の合成円柱を厳密に回収する。 -/
lemma relativeKanHomotopySpanComposite_restrict {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E))) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeKanHomotopySpanComposite j a b t).h =
      (relativeKanHomotopySpanBoundary j a b t).h := by
  change (j ▷ (Δ[1] : SSet.{u})) ≫ MonoidalClosed.uncurry
    (SSet.yonedaEquiv.symm (relativeKanHomotopySpanData j a b t).data.edge.edge) =
      MonoidalClosed.uncurry (SSet.yonedaEquiv.symm t.edge.edge)
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  rw [(relativeKanHomotopySpanData j a b t).composite_edge]

/-- 境界の指定合成辺が恒等なら、全合成円柱は境界上で厳密に定数になる。 -/
lemma relativeKanHomotopySpanComposite_restrict_constant {T U E : SSet.{u}} [KanComplex E]
    (j : T ⟶ U) [Mono j] {D F G : U ⟶ E}
    (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
    (t : KanSpanTriangleData
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E))
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E)))
    (ht : t.edge.edge = (SSet.Truncated.Edge.id
      (X := (truncation 2).obj ((ihom T).obj E)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F))).edge) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeKanHomotopySpanComposite j a b t).h =
      CartesianMonoidalCategory.fst T (Δ[1] : SSet.{u}) ≫ j ≫ F := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyOfFunctorEdge_pre_eq_constant j (j ≫ F)
    (relativeKanHomotopySpanData j a b t).data.edge.toTruncated
    ((relativeKanHomotopySpanData j a b t).composite_edge.trans ht)

end SerrePositivity.KST.SConstruction
