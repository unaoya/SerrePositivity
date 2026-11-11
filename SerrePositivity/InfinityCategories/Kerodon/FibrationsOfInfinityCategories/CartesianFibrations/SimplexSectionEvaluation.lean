module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorOverEvaluationComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningSectionNaturality

/-!
概要：単体圏の共同切断評価の制限を実際の fiber 評価へ接続する。
方針：全高次の比較の辺と、底上の可換三角形の評価の合成則を使う。
規約：端点の輸送を明示し、元の比較の辺を保つ。
使われ方：共同降下の自然性から既存 transport を回収する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：単体作用素の制限の辺は、共同切断の端点同定と可換。
方針：辺そのものの一致をホモトピー圏の両端の輸送へ移す。
規約：端点の等式は既存の共同評価の頂点公式。
使われ方：制限の辺の後に実際の頂点評価を合成する準備。 -/
lemma transportSimplexSectionInfinity_restriction_hom {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex (B.map α.op σ))) =
    eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex (B.map α.op σ))
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).toTruncated)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeFunctorOverPreComparison
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op))).toTruncated)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSimplexSectionInfinity_edge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ))
  apply (cancel_epi (eqToHom (congrArg HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)).symm)).1
  simpa only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
    SSet.Edge.toTruncated] using h

/-- 概要：共同切断の制限の後の fiber 評価は像の頂点での評価と一致。
方針：端点を同定してから底上の可換三角形の評価の合成則を使う。
規約：単体作用素は面・退化を含め任意。
使われ方：共同降下の自然性の右辺を実際の fiber 評価へ置き換える。 -/
lemma transportSimplexSectionInfinity_restriction_evaluate {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n))
    (v : (stdSimplex.obj m) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity B)).toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex (B.map α.op σ))) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm (B.map α.op σ)) v) ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op).w) v)) =
    eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((stdSimplex.map α).app (Opposite.op ⦋0⦌) v)) := by
  rw [← Category.assoc _ (eqToHom _) _, transportSimplexSectionInfinity_restriction_hom]
  rw [Category.assoc]
  congr 1
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorOverPreComparisonEdge_evaluate (SSet.yonedaEquiv.symm σ)
    (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op).w) v

/-- 概要：共同降下の自然性を実際の fiber 評価へ接続する。
方針：同じ降下同型の自然性の正方形へ、切断制限の評価公式を合成する。
規約：全対象上の同じ同型と実際の比較の辺を保つ。
使われ方：底の一単体の両端で既存 transport を回収する。 -/
lemma leftStraighteningSectionJointDiagram_restriction_evaluate {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n))
    (v : (stdSimplex.obj m) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanEnrichedDiagramIndexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ)).map
          ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B)).toTruncated ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (B.map α.op σ))))).hom ≫
      eqToHom (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex (B.map α.op σ))) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm (B.map α.op σ)) v) ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b)))
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexDomainFunctor B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexRestriction α σ).op).w) v)) =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ)))).hom ≫
    eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((stdSimplex.map α).app (Opposite.op ⦋0⦌) v)) := by
  rw [← Category.assoc _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app _).hom _,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso_naturality, Category.assoc]
  rw [transportSimplexSectionInfinity_restriction_evaluate]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
