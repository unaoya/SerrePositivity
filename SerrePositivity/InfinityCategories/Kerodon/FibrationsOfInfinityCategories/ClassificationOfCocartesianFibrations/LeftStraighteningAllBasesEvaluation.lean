module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorEvaluationComparison

/-!
概要：任意の底の straightening を、全 left fibrations 上で実際の fiber 評価と比較する。
方針：共同降下の比較を各単体の初頂点で評価し、切断の始点評価の同型へ接続する。
規約：対象ごとの同値だけでなく、全パラメーター上の大域的な関手同型を保持する。
使われ方：既存 transport・相対表現・単位と余単位の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 二変数を交換した関手を一点で評価すると、交換前のその点での値を回収する。 -/
lemma internalHomFlipHomEquiv_evaluate_vertex {A C X : SSet.{u}}
    (f : A ⟶ (ihom C).obj X) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A C X f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) =
      f.app (Opposite.op ⦋0⦌) a := by
  have he := congrArg (fun m ↦ m.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate A C X a)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A C X f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom C).obj X) a).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at he
  exact he

/-- straightening の初頂点の値は、共同降下の同じ頂点の値と厳密に一致する。 -/
lemma leftStraighteningInfinityMap_simplexFirstVertex_vertex {B : SSet.{u}}
    {n : SimplexCategory} (σ : B.obj (Opposite.op n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (ULift.up ((SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1)))))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋0⦌)
      (((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap, internalHomFlipHomEquiv_evaluate_vertex]
  exact congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram B).app (Opposite.op ⦋0⦌))
    (congrArg ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_vertex σ)).symm

/-- 任意の単体の初頂点での straightening は、その単体上の切断評価と関手同型。 -/
def leftStraighteningInfinityMap_simplexFirstVertexIso {B : SSet.{u}} {n : SimplexCategory}
    (σ : B.obj (Opposite.op n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up ((SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1))))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEnrichedEvaluation (Over.mk (SSet.yonedaEquiv.symm σ)))) :=
  eqToIso (congrArg HomotopyCategory.mk
    (leftStraighteningInfinityMap_simplexFirstVertex_vertex σ)) ≪≫
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
    (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ))) ≪≫
  eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ))

/-- straightening の単体の初頂点での評価は、実際の fiber 評価と全対象上で関手同型。 -/
def leftStraighteningInfinityMap_firstVertexFiberIso {B : SSet.{u}} {n : SimplexCategory}
    (σ : B.obj (Opposite.op n)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        (ULift.up ((SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1))))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation ((SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin (n.len + 1))))) :=
  leftStraighteningInfinityMap_simplexFirstVertexIso σ ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso (SSet.yonedaEquiv.symm σ) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n.len)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex_leftAnodyne n.len)

/-- 最初の頂点の包含は、標準零単体の頂点を指定された最初の頂点へ送る。 -/
lemma scaffoldFirstVertex_app_zero (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex.{u} n).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) =
      stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1)) := by
  change (stdSimplex.obj ⦋n⦌).map (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down.op
    (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))) = _
  have hh : (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down = 𝟙 ⦋0⦌ :=
    @Subsingleton.elim ((⦋0⦌ : SimplexCategory) ⟶ ⦋0⦌) inferInstance _ _
  rw [hh, op_id, Functor.map_id_apply]

/-- 単体の初頂点の fiber 比較の射は、既存の共同降下の成分と切断評価の合成。 -/
lemma leftStraighteningInfinityMap_firstVertexFiberIso_hom {B : SSet.{u}}
    {n : SimplexCategory} (σ : B.obj (Opposite.op n)) :
    (leftStraighteningInfinityMap_firstVertexFiberIso σ).hom =
      eqToHom (congrArg HomotopyCategory.mk
        (leftStraighteningInfinityMap_simplexFirstVertex_vertex σ)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningSectionJointDiagram_restrictIso B).app
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex σ)))).hom ≫
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexSectionInfinity_vertex σ)) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge (SSet.yonedaEquiv.symm σ)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.scaffoldFirstVertex n.len).app (Opposite.op ⦋0⦌)
            (stdSimplex.obj₀Equiv.symm 0))) := by
  simp only [leftStraighteningInfinityMap_firstVertexFiberIso,
    leftStraighteningInfinityMap_simplexFirstVertexIso, Iso.trans_hom, eqToIso.hom,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonIso, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparisonIso, asIso_hom,
    Category.assoc, SSet.Edge.toTruncated,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorEvaluationComparisonEdge]

/-- 任意の底の頂点での straightening は、全 left fibrations の実際の fiber 評価と関手同型。 -/
def leftStraighteningInfinityMap_evaluateIso {B : SSet.{u}} (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up b))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b) := by
  have hb : (SSet.yonedaEquiv.symm b).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = b := by
    change B.map (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down.op b = b
    have hh : (stdSimplex.obj₀Equiv.symm (0 : Fin 1)).down = 𝟙 ⦋0⦌ :=
      @Subsingleton.elim ((⦋0⦌ : SimplexCategory) ⟶ ⦋0⦌) inferInstance _ _
    rw [hh, op_id, Functor.map_id_apply]
  exact (eqToIso (congrArg (fun c ↦ HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up c)))) hb)).symm ≪≫
    leftStraighteningInfinityMap_firstVertexFiberIso b ≪≫
    eqToIso (congrArg (fun c ↦ HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation c))) hb)

/-- 頂点の評価同型は、零単体の fiber 比較と同じホモトピー圏の射を表す。 -/
lemma leftStraighteningInfinityMap_evaluateIso_arrow {B : SSet.{u}} (b : B _⦋0⦌) :
    Arrow.mk (leftStraighteningInfinityMap_evaluateIso b).hom =
      Arrow.mk (leftStraighteningInfinityMap_firstVertexFiberIso b).hom := by
  unfold leftStraighteningInfinityMap_evaluateIso
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv,
    ← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
