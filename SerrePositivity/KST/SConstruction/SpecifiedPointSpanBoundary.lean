module
public import SerrePositivity.KST.SConstruction.RelativeKanOuterSpanFamilies
public import SerrePositivity.KST.SConstruction.CoherentHomotopyComponentCalculus
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.FunctorIsoPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor

/-! # 元の一点の指定外側三角形を関手空間の境界へ戻す
概要：元の二円柱の指定頂点の成分を保持し、元の比較辺と三角形を一点の境界データへ移す。
方針：一点の関手空間の厳密な評価同型を用い、全三面を同じ元の成分辺へ照合する。
規約：指定三角形を選び直さず、Kan 性は境界構成には要求しない。
使われ方：元の K の指定適合辺を全精密化パラメータへ延長する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の頂点の一点表示は単射である。 -/
instance specifiedParameterPoint_mono {U : SSet.{u}} (u : U _⦋0⦌) :
    Mono (SSet.yonedaEquiv.symm u) := stdSimplex.isTerminalObj₀.mono_from _

/-- 関手の辺の一点への制限は、同じ元の成分辺を評価同型の逆で戻したもの。 -/
lemma specifiedPointRestriction_edge {U E : SSet.{u}} {D F : U ⟶ E}
    (H : SSet.Homotopy D F) (u : U _⦋0⦌) :
    ((pre (SSet.yonedaEquiv.symm u)).app E).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H u).edge := by
  apply (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom.app (Opposite.op ⦋1⦌))).mp
    (by infer_instance)
  have h := congrArg (fun q => q.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointPrecomp_evaluation (X := E) u)
  have hv := homotopyVertexEdge_yoneda H u
  rw [SSet.yonedaEquiv_comp] at hv
  have hi := congrArg (fun q => q.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H u).edge) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv_hom_id
  exact h.trans (hv.trans hi.symm)

/-- 元の指定比較辺を、一点での同じ定数終点の間の関手の辺へ戻す。 -/
def specifiedPointSpanEdge {U E : SSet.{u}} (u : U _⦋0⦌) {x y : E _⦋0⦌} (e : E.Edge x y) :
    ((ihom (Δ[0] : SSet.{u})).obj E).Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm u ≫ SSet.const x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm u ≫ SSet.const y)) :=
  (e.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex (Δ[0] : SSet.{u}) x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex (Δ[0] : SSet.{u}) y)

/-- 元の全三面を保持した指定三角形を、一点の関手空間の同じ外側三角形へ戻す。 -/
def specifiedPointSpanTriangle {U E : SSet.{u}} (u : U _⦋0⦌) {D : U ⟶ E}
    {x y : E _⦋0⦌} (a : SSet.Homotopy D (SSet.const x))
    (b : SSet.Homotopy D (SSet.const y)) (e : E.Edge x y) (t : E _⦋2⦌)
    (h₂ : E.map (SimplexCategory.δ (2 : Fin 3)).op t =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge a u).edge)
    (h₀ : E.map (SimplexCategory.δ (0 : Fin 3)).op t = e.edge)
    (h₁ : E.map (SimplexCategory.δ (1 : Fin 3)).op t =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge b u).edge) :
    SSet.Edge.CompStruct
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map
        ((pre (SSet.yonedaEquiv.symm u)).app E)) (specifiedPointSpanEdge u e)
      ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map
        ((pre (SSet.yonedaEquiv.symm u)).app E)) := by
  refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋2⦌) t, ?_, ?_, ?_⟩
  · exact (NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv
      (SimplexCategory.δ (2 : Fin 3)).op t).symm.trans
        ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋1⦌)) h₂).trans
          (specifiedPointRestriction_edge a u).symm)
  · exact (NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv
      (SimplexCategory.δ (0 : Fin 3)).op t).symm.trans
        (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋1⦌)) h₀)
  · exact (NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv
      (SimplexCategory.δ (1 : Fin 3)).op t).symm.trans
        ((congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app (Opposite.op ⦋1⦌)) h₁).trans
          (specifiedPointRestriction_edge b u).symm)

/-- 一点の関手空間へ戻した元の単体の評価は、元の単体の一点に定数な族。 -/
lemma specifiedPointSimplex_uncurry {E : SSet.{u}} {n : ℕ} (s : E _⦋n⦌) :
    uncurry (SSet.yonedaEquiv.symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).inv.app
      (Opposite.op ⦋n⦌) s)) =
      snd (Δ[0] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ SSet.yonedaEquiv.symm s := by
  rw [← SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm s ≫ curry (snd (Δ[0] : SSet.{u}) E)) = _
  rw [uncurry_natural_left, uncurry_curry, whiskerLeft_snd]

end SerrePositivity.KST.SConstruction
