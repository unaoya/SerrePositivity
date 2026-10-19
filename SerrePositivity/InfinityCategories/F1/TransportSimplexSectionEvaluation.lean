module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverEvaluationComparison
public import SerrePositivity.InfinityCategories.F1.LeftStraighteningSectionNaturality

/-!
概要：単体圏の共同切断評価の制限を実際の fiber 評価へ接続する。
方針：全高次の比較の辺と、底上の可換三角形の評価の合成則を使う。
規約：端点の輸送を明示し、元の比較の辺を保つ。
使われ方：共同降下の自然性から既存 transport を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体作用素の制限の辺は、共同切断の端点同定と可換。
方針：辺そのものの一致をホモトピー圏の両端の輸送へ移す。
規約：端点の等式は既存の共同評価の頂点公式。
使われ方：制限の辺の後に実際の頂点評価を合成する準備。 -/
lemma transportSimplexSectionInfinity_restriction_hom {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n)) :
    SSet.Truncated.HomotopyCategory.homMk
        ((kanEnrichedDiagramIndexEdge (transportSimplexRestriction α σ)).map
          (transportSimplexSectionInfinity B)).toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk
        (transportSimplexSectionInfinity_vertex (B.map α.op σ))) =
    eqToHom (congrArg HomotopyCategory.mk (transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (kanEnrichedComparisonEdge (relativeFunctorOverPreComparison
          ((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op))) := by
  have h := homMk_transport
    (transportSimplexSectionInfinity_vertex σ)
    (transportSimplexSectionInfinity_vertex (B.map α.op σ))
    (((kanEnrichedDiagramIndexEdge (transportSimplexRestriction α σ)).map
      (transportSimplexSectionInfinity B)).toTruncated)
    ((kanEnrichedComparisonEdge (relativeFunctorOverPreComparison
      ((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op))).toTruncated)
    (transportSimplexSectionInfinity_edge (transportSimplexRestriction α σ))
  apply (cancel_epi (eqToHom (congrArg HomotopyCategory.mk
    (transportSimplexSectionInfinity_vertex σ)).symm)).1
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
        ((kanEnrichedDiagramIndexEdge (transportSimplexRestriction α σ)).map
          (transportSimplexSectionInfinity B)).toTruncated ≫
      eqToHom (congrArg HomotopyCategory.mk
        (transportSimplexSectionInfinity_vertex (B.map α.op σ))) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm (B.map α.op σ)) v) ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (functorVertex (leftFibrationInfinityFiberEvaluation b)))
        (overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
          (((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op).w) v)) =
    eqToHom (congrArg HomotopyCategory.mk (transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((stdSimplex.map α).app (Opposite.op ⦋0⦌) v)) := by
  rw [← Category.assoc _ (eqToHom _) _, transportSimplexSectionInfinity_restriction_hom]
  rw [Category.assoc]
  congr 1
  exact relativeFunctorOverPreComparisonEdge_evaluate (SSet.yonedaEquiv.symm σ)
    (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
    (((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op).w) v

/-- 概要：共同降下の自然性を実際の fiber 評価へ接続する。
方針：同じ降下同型の自然性の正方形へ、切断制限の評価公式を合成する。
規約：全対象上の同じ同型と実際の比較の辺を保つ。
使われ方：底の一単体の両端で既存 transport を回収する。 -/
lemma leftStraighteningSectionJointDiagram_restriction_evaluate {B : SSet.{u}}
    {m n : SimplexCategory} (α : m ⟶ n) (σ : B.obj (Opposite.op n))
    (v : (stdSimplex.obj m) _⦋0⦌) :
    SSet.Truncated.HomotopyCategory.homMk
        ((kanEnrichedDiagramIndexEdge (transportSimplexRestriction α σ)).map
          ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
            leftStraighteningSectionJointDiagram B)).toTruncated ≫
      ((leftStraighteningSectionJointDiagram_restrictIso B).app
        (ULift.up (nerveVertex (transportSimplexIndex (B.map α.op σ))))).hom ≫
      eqToHom (congrArg HomotopyCategory.mk
        (transportSimplexSectionInfinity_vertex (B.map α.op σ))) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm (B.map α.op σ)) v) ≫
      eqToHom (congrArg (fun b ↦ HomotopyCategory.mk
        (functorVertex (leftFibrationInfinityFiberEvaluation b)))
        (overPreEvaluationVertex (SSet.yonedaEquiv.symm σ)
          (SSet.yonedaEquiv.symm (B.map α.op σ)) (stdSimplex.map α)
          (((transportSimplexDomainFunctor B).map (transportSimplexRestriction α σ).op).w) v)) =
    ((leftStraighteningSectionJointDiagram_restrictIso B).app
      (ULift.up (nerveVertex (transportSimplexIndex σ)))).hom ≫
    eqToHom (congrArg HomotopyCategory.mk (transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((stdSimplex.map α).app (Opposite.op ⦋0⦌) v)) := by
  rw [← Category.assoc _
    ((leftStraighteningSectionJointDiagram_restrictIso B).app _).hom _,
    leftStraighteningSectionJointDiagram_restrictIso_naturality, Category.assoc]
  rw [transportSimplexSectionInfinity_restriction_evaluate]

end SerrePositivity.InfinityCategories

