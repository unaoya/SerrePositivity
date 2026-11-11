module
public import SerrePositivity.KST.SConstruction.VertexDiscretePinchedFamilies
public import SerrePositivity.KST.SConstruction.FixedEndpointRestrictionCorrection

/-! # 離散頂点上の変換の指定辺と射の類の検出
概要：指定した対象ごとの辺を一つの変換の辺へ束ね、射の類を各座標で検出する。
方針：関数単体と固定端点の座標表示を使う。
規約：対象の集合は任意で、無限個の座標も同時に扱う。
使われ方：元の構造射を全対象上で同時に指定する全体補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 離散部分上の射の零次族から元の関手頂点を復元する。 -/
lemma vertexDiscreteFunctionSimplex_vertex {A X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => F.app (Opposite.op ⦋0⦌) a) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F := by
  have he : (fun a => F.app (Opposite.op ⦋0⦌) a) =
      (fun a => (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F)) := rfl
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex he).trans (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_reconstruct _)

/-- 元の各対象の指定辺を持つ、離散部分上の一つの変換の辺。 -/
def vertexDiscreteSpecifiedEdge {A X : SSet.{u}} (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A ⟶ X)
    (e : ∀ a : A _⦋0⦌, X.Edge (F.app (Opposite.op ⦋0⦌) a) (G.app (Opposite.op ⦋0⦌) a)) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) where
  edge := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => (e a).edge)
  src_eq := by
    change ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X).map (SimplexCategory.δ (1 : Fin 2)).op
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => (e a).edge)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map]
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (funext (fun a => (e a).src_eq))).trans
      (vertexDiscreteFunctionSimplex_vertex F)
  tgt_eq := by
    change ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X).map (SimplexCategory.δ (0 : Fin 2)).op
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (fun a => (e a).edge)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_map]
    exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex (funext (fun a => (e a).tgt_eq))).trans
      (vertexDiscreteFunctionSimplex_vertex G)

/-- 指定辺の全体化は各座標で元の辺の一単体を厳密に回収する。 -/
lemma vertexDiscreteSpecifiedEdge_evaluate {A X : SSet.{u}} (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A ⟶ X)
    (e : ∀ a : A _⦋0⦌, X.Edge (F.app (Opposite.op ⦋0⦌) a) (G.app (Opposite.op ⦋0⦌) a))
    (a : A _⦋0⦌) :
    ((vertexDiscreteSpecifiedEdge F G e).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a))).edge =
      (e a).edge := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteFunctionSimplex_evaluate _ a

/-- 離散部分上の変換の射の類は、全ての対象で評価した射の類で検出できる。 -/
lemma vertexDiscreteFunctorEdge_hom_ext {A X : SSet.{u}} [Quasicategory X]
    (f g : ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X) _⦋0⦌)
    (e k : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete A)).obj X)) f g)
    (h : ∀ a : A _⦋0⦌, SSet.Truncated.HomotopyCategory.homMk
      (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a))) =
        SSet.Truncated.HomotopyCategory.homMk (k.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a)))) :
    SSet.Truncated.HomotopyCategory.homMk e = SSet.Truncated.HomotopyCategory.homMk k := by
  let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).symm e
  let w := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).symm k
  have hp : SSet.π₀.mk v = SSet.π₀.mk w := by
    apply vertexDiscretePinched_piZero_injective f g
    intro a
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom_injective _ _
    change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _ _) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _ _)
    have he := (diagramPinchedVertex_map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) v).trans
      (congrArg (fun q => q.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).apply_symm_apply e))
    have hk := (diagramPinchedVertex_map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a) w).trans
      (congrArg (fun q => q.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.vertexDiscreteEvaluate a)))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).apply_symm_apply k))
    exact (congrArg SSet.Truncated.HomotopyCategory.homMk he).trans
      ((h a).trans (congrArg SSet.Truncated.HomotopyCategory.homMk hk).symm)
  have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom f g) hp
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g v) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g w) at hh
  exact (congrArg₂ Eq
    (congrArg SSet.Truncated.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).apply_symm_apply e))
    (congrArg SSet.Truncated.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv f g).apply_symm_apply k))).mp hh

end SerrePositivity.KST.SConstruction
