module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBasesEvaluation

/-!
概要：共同降下の制限の辺を、指定された straightening の評価を両端として表示する。
方針：両端の厳密な等式で辺を輸送し、既存の同型の射の公式を使う。
規約：元の一単体と降下同型を選び直さない。
使われ方：指定済みの fiber 比較を使った transport の回収。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：辺の端点の等式による輸送はホモトピー圏で等式の射による共役。
方針：同じ一単体を持つ二つの辺の輸送公式を使う。
規約：辺の代表を保持する。
使われ方：共同降下の辺の両端を指定済みの評価へ揃える。 -/
lemma homMk_edge_ofEq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (e : SSet.Edge x y) (hx : x = x') (hy : y = y') :
    SSet.Truncated.HomotopyCategory.homMk (e.ofEq hx hy).toTruncated =
      eqToHom (congrArg HomotopyCategory.mk hx).symm ≫
      SSet.Truncated.HomotopyCategory.homMk e.toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk hy) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hx hy e.toTruncated (e.ofEq hx hy).toTruncated rfl).symm

/-- 概要：単体の制限の辺を straightening の指定評価を両端として表示する。
方針：共同降下の実際の辺の端点だけを厳密な頂点公式で揃える。
規約：一単体そのものは変更しない。
使われ方：既存の fiber 比較の同型へ合成する辺。 -/
def leftStraighteningInfinityMap_simplexRestrictionEdge {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    SSet.Edge
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up ((SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1)))))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up ((SSet.yonedaEquiv.symm (B.map α.op σ)).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin (m.len + 1))))))) :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B))).ofEq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexFirstVertex_vertex σ).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexFirstVertex_vertex (B.map α.op σ)).symm

/-- 概要：制限の辺の射は、共同降下の辺の射の指定された端点輸送。
方針：端点だけを変更する辺の一般公式を使う。
規約：両端は既存の fiber 比較の始域。
使われ方：fiber 比較の合成で端点の等式を消去する。 -/
lemma leftStraighteningInfinityMap_simplexRestrictionEdge_hom {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    SSet.Truncated.HomotopyCategory.homMk
        (leftStraighteningInfinityMap_simplexRestrictionEdge α σ).toTruncated =
    eqToHom (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexFirstVertex_vertex σ)) ≫
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
          ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B)).toTruncated ≫
    eqToHom (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexFirstVertex_vertex (B.map α.op σ))).symm :=
  homMk_edge_ofEq _ _ _

/-- 概要：指定された fiber 同型を使った制限の辺の評価公式。
方針：端点の等式を消去し、共同降下の自然性の評価公式を使う。
規約：既存の firstVertexFiberIso をそのまま合成する。
使われ方：始点と終点への制限で既存 transport を比較する。 -/
lemma leftStraighteningInfinityMap_simplexRestrictionEdge_evaluate {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    SSet.Truncated.HomotopyCategory.homMk
        (leftStraighteningInfinityMap_simplexRestrictionEdge α σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso (B.map α.op σ)).hom ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op).w)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m.len).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm 0)))) =
    eqToHom (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_simplexFirstVertex_vertex σ)) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ)))).hom ≫
    eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((stdSimplex.map α).app (Opposite.op ⦋0⦌)
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex m.len).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm 0)))) := by
  rw [leftStraighteningInfinityMap_simplexRestrictionEdge_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso_hom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftStraighteningSectionJointDiagram_restriction_evaluate]

/-- 概要：終点への制限の辺は、指定済みの fiber 同型で既存 transport を回収する。
方針：一般の評価公式の終点を、切断の始点評価と transport の合成に置き換える。
規約：既存の transport の辺と firstVertexFiberIso を使う。
使われ方：元の底の辺への straightening の作用の比較。 -/
lemma leftStraighteningInfinityMap_terminalRestriction_transport {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (leftStraighteningInfinityMap_simplexRestrictionEdge
          (SimplexCategory.δ (0 : Fin 2)) σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso
        (B.map (SimplexCategory.δ (0 : Fin 2)).op σ)).hom ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map (SimplexCategory.δ (0 : Fin 2)).op σ))
          (stdSimplex.map (SimplexCategory.δ (0 : Fin 2)))
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (0 : Fin 2)) σ).op).w)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 0).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm 0)))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso σ).hom ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge (SSet.yonedaEquiv.symm σ)) := by
  calc
    _ = _ := leftStraighteningInfinityMap_simplexRestrictionEdge_evaluate
      (SimplexCategory.δ (0 : Fin 2)) σ
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso_hom]
      simp only [Category.assoc]
      congr 3
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationNaturalTransportEdge_source (SSet.yonedaEquiv.symm σ)).symm

/-- 概要：始点への制限は一単体とその始点で指定された fiber 同型を結ぶ。
方針：一般の評価公式を始点に特殊化する。
規約：同じ firstVertexFiberIso の射に関する等式。
使われ方：終点での transport 比較の始点側の同型を揃える。 -/
lemma leftStraighteningInfinityMap_initialRestriction_fiberIso {B : SSet.{u}}
    (σ : B _⦋1⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        (leftStraighteningInfinityMap_simplexRestrictionEdge
          (SimplexCategory.δ (1 : Fin 2)) σ).toTruncated ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso
        (B.map (SimplexCategory.δ (1 : Fin 2)).op σ)).hom ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map (SimplexCategory.δ (1 : Fin 2)).op σ))
          (stdSimplex.map (SimplexCategory.δ (1 : Fin 2)))
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction (SimplexCategory.δ (1 : Fin 2)) σ).op).w)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex 0).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm 0)))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso σ).hom := by
  conv_rhs => rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap_firstVertexFiberIso_hom]
  exact leftStraighteningInfinityMap_simplexRestrictionEdge_evaluate
    (SimplexCategory.δ (1 : Fin 2)) σ

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
