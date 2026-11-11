module

public import SerrePositivity.KST.Spectra.SpectrumCircleLoopDiagramFamily

/-!
概要：元の円の loop 図式族の始点と終点を、元の二つの Sp の関手へ厳密同定する。
方針：元の参照三角形の全族の両端の式を使う。
規約：全次数の射の等式。使われ方：native loop と円 cotensor の高次自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 元の四角形族の参照三角形の全ての頂点の評価。 -/
lemma circleSquareFamily_reference_vertex (i : Fin 3) :
    lift (𝟙 Sp.{u}) (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm i))) ≫ nativeCircleEvaluationSquareFamily =
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm i)) ≫
      nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle := by
  rw [← nativeCircleEvaluationSquareFamily_upper, ← Category.assoc, lift_map,
    Category.id_comp, SSet.const_comp]

/-- 元の loop 図式族の始点の全関手は、元の native な円 cotensor。 -/
lemma circleLoopDiagramFamily_source :
    circleLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 0 0 =
      nativeCotensor PointedSimplicialSet.circle := by
  have h := circleSquareFamily_reference_vertex.{u} 0
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) =
      (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
    apply Prod.ext <;> decide
  rw [hs, nativeZeroEvaluationTriangleFamily_zero] at h
  rw [circleLoopDiagramFamily_evaluation]
  exact h

/-- 元の loop 図式族の終点の全関手は、元の共通解像の逆と源射影の合成。 -/
lemma circleLoopDiagramFamily_target :
    circleLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1 =
      (CotensorCompatible.sourceInfinityEquivalence PointedSimplicialSet.circle).inv ≫
        CotensorCompatible.sourceInfinityMap PointedSimplicialSet.circle := by
  have h := circleSquareFamily_reference_vertex.{u} 2
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 1} 0).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (2 : Fin 3)) =
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1) := by
    apply Prod.ext <;> decide
  rw [hs, nativeZeroEvaluationTriangleFamily_two] at h
  rw [circleLoopDiagramFamily_evaluation]
  exact h

/-- 元の全 loop 図式族の終点は、元の恒等関手と実際に関手同型。 -/
def circleLoopDiagramFamily_targetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (circleLoopDiagramFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation Sp.{u} 1 1) (𝟙 Sp.{u}) := by
  rw [circleLoopDiagramFamily_target]
  exact (CotensorCompatible.sourceInfinityEquivalence PointedSimplicialSet.circle).invHomIso

end SerrePositivity.KST.Spectra.OmegaSpectrum
