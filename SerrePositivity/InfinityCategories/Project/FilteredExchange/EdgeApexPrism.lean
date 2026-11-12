module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：元の native な辺を、その全一単体を保持する頂点輸送円柱にする。
方針：標準区間への第一射影と辺の Yoneda 表示を合成する。
規約：元の辺を代表の選択で置き換えない。使われ方：元の Kan 比較辺による極限頂点の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)

/-- 概要：元の辺を区間と点の積からの頂点円柱にする。
方針：第一射影と Yoneda 表示。規約：辺の全単体。使われ方：指定頂点輸送の入力。 -/
def edgeApexPrism : (Δ[1] : SSet.{u}) ⊗ (Δ[0] : SSet.{u}) ⟶ X :=
  fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge

/-- 概要：頂点円柱の始点は元の辺の始点。
方針：零端の面を評価。規約：厳密な射の式。使われ方：輸送後の錐頂点。 -/
lemma edgeApexPrism_zero : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[0] : SSet.{u}) ≫ edgeApexPrism e =
    SSet.yonedaEquiv.symm x := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[0] : SSet.{u}) ≫
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) = stdSimplex.δ (1 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [edgeApexPrism, ← Category.assoc, hp, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm e.src_eq

/-- 概要：頂点円柱の終点は元の辺の終点。
方針：一端の面を評価。規約：厳密な射の式。使われ方：元の錐頂点との照合。 -/
lemma edgeApexPrism_one : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[0] : SSet.{u}) ≫ edgeApexPrism e =
    SSet.yonedaEquiv.symm y := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[0] : SSet.{u}) ≫
      fst (Δ[1] : SSet.{u}) (Δ[0] : SSet.{u}) = stdSimplex.δ (0 : Fin 2) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [edgeApexPrism, ← Category.assoc, hp, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm e.tgt_eq

/-- 概要：元の可逆辺の頂点円柱の全垂直辺は可逆。
方針：区間の恒等単体で元の辺を回収。規約：標的の充填性不要。使われ方：極限錐の輸送。 -/
lemma edgeApexPrism_vertical_isInvertible (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e)
    (z : (Δ[0] : SSet.{u}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((edgeApexPrism e).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1))) := by
  have h : (edgeApexPrism e).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant z 1) = e.edge := by
    exact SSet.yonedaEquiv_symm_app_id e.edge
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex _) (f := e.toTruncated) h).mpr he

end SerrePositivity.InfinityCategories.Project.FilteredExchange
