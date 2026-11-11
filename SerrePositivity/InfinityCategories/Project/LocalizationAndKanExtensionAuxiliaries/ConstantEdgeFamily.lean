module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConstantFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom

/-!
概要：一つの実辺の定数パラメータ族を、同じ実辺の定値関手への像に同定する。
方針：点上の区間比較を展開し、第二射影と curry の自然性を使う。
規約：辺の代表と全パラメータを保持する。使われ方：反転される実分母の定数族。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
/-- 辺の定数族の区間表示は、時間への射影の後に同じ辺を続けた写像。 -/
lemma intervalFamilyHomotopy_const_edge_h {K X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e))).h =
      snd K (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge := by
  have hc : (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) : K ⟶ _) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda _).symm
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy]
  rw [hc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge_uncurry]
  have hp : (β_ K (Δ[1] : SSet.{u})).hom ≫
      (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⟶ Δ[0])) ≫
        fst (Δ[1] : SSet.{u}) Δ[0] = snd K (Δ[1] : SSet.{u}) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  simpa only [Category.assoc] using congrArg (fun k => k ≫ SSet.yonedaEquiv.symm e.edge) hp
/-- 実辺の定数族は、同じ辺の Hom 類を定値関手へ送ったものに厳密に一致する。 -/
lemma intervalFamilyHom_const_edge {K X : SSet.{u}} {x y : X _⦋0⦌}
    (e : X.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk e.toTruncated) := by
  symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K y)
    (e.toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e)))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X).app (Opposite.op ⦋1⦌) e.edge =
    SSet.yonedaEquiv (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomotopy
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge e))).h)
  rw [intervalFamilyHomotopy_const_edge_h]
  have he : SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge) = e.edge :=
    SSet.yonedaEquiv.apply_symm_apply e.edge
  conv_lhs => rw [← he, ← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap, uncurry_curry]
  rfl
/-- 実 pinched 頂点の定数族も、その同じ実辺の定値関手への像を表す。 -/
lemma pinchedFamilyHom_const_vertex {K X : SSet.{u}} {x y : X _⦋0⦌}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (SSet.const (X := K) s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y s)) := by
  rw [SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_vertex]
  exact intervalFamilyHom_const_edge (SSet.Edge.ofTruncated (X := X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y s))
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
