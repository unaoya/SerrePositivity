module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoVertexEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：全族の関手同型の成分を、一点への係数制限と単体的評価の同じ像に照合する。
方針：ホモトピー評価の関手の一致を Arrow へ移し、端点表示の等式だけを消去する。
規約：始域の充填性は要求しない。使われ方：固定延長の全終端辺輸送の成分の計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

private lemma arrow_eqToHom_comp {C : Type*} [Category* C] {a b c d : C}
    (ha : a = b) (f : b ⟶ c) (hd : c = d) :
    Arrow.mk (eqToHom ha ≫ f ≫ eqToHom hd) = Arrow.mk f := by
  subst b d
  simp

/-- 関手同型の成分の射は、同じ頂点評価で写した射と端点表示を除いて一致する。 -/
lemma functorIsoComponent_hom_arrow {A X : SSet.{u}} {f g : A ⟶ X}
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : A _⦋0⦌) :
    Arrow.mk (I.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).hom := by
  have h := congrArg (fun F ↦ F.mapArrow.obj (Arrow.mk I.hom))
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorHomotopyEvaluation_evaluate (X := X) x)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.toNatIso, Iso.trans_hom, Iso.symm_hom, eqToIso,
    NatTrans.comp_app, eqToHom_app]
  simp only [eqToHom_app]
  rw [arrow_eqToHom_comp]
  exact h

/-- 頂点の一点表示で前合成してから評価すると、同じ元の頂点での評価となる。 -/
lemma pointPrecomp_evaluation {A X : SSet.{u}} (x : A _⦋0⦌) :
    (pre (SSet.yonedaEquiv.symm x)).app X ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.evaluateFunctorAt_precomp]
  congr 1
  rw [SSet.yonedaEquiv_symm_zero]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero x

/-- 全族の同型の成分は、一点へ制限した同じ同型を評価した射そのもの。 -/
lemma functorIsoComponent_point_hom_arrow {A X : SSet.{u}} {f g : A ⟶ X}
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (x : A _⦋0⦌) :
    Arrow.mk (I.toNatIso.hom.app (SSet.HomotopyCategory.mk x)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp I (SSet.yonedaEquiv.symm x))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).hom := by
  rw [functorIsoComponent_hom_arrow]
  change Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).hom =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I ((pre (SSet.yonedaEquiv.symm x)).app X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso X).hom).hom
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexIso_map_comp]
  exact (congrArg (fun k : (ihom A).obj X ⟶ X ↦
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map I k).hom) (pointPrecomp_evaluation (X := X) x)).symm

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
