module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePostcomposeEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquarePrecomposeEdge
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SliceSquareDiagramFixed
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ColimitSquareComparison

/-! # 前合成・後合成の四角形比較辺の端点成分

概要：四角形全体の辺を始点・終点で評価し、指定した鎖写像または定値辺へ同定する。
方針：slice/coslice の図式表示の評価式と、実際の辺の射影の式を使う。
規約：端点の表示変更に依存しない一単体の等式。使われ方：D7 の suspension の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded SSet
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {V A B C D E : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D)

/-- 終点を後合成する四角形比較の終点成分は指定射 q。 -/
lemma postcomposeSquareEdge_target (q : D ⟶ E) :
    ((s.postcomposeSquareEdge q).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge q).edge := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)).app _
        (s.postcomposeSliceEdge q).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_targetEvaluation]
  exact s.postcomposeSliceEdge_projection q

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (postcomposeSquareEdge_target)


/-- 終点を後合成する四角形比較の始点成分は定値辺。 -/
lemma postcomposeSquareEdge_source (q : D ⟶ E) :
    ((s.postcomposeSquareEdge q).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)))).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.spanSourceEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square))) 1 := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)).app _
        (s.postcomposeSliceEdge q).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cosliceSquareDiagramMap_sourceEvaluation]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (postcomposeSquareEdge_source)


/-- 始点を前合成する四角形比較の始点成分は指定射 p。 -/
lemma precomposeSquareEdge_source (p : V ⟶ A) :
    ((s.precomposeSquareEdge p).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)))).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge p).edge := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 0 0)).app _
        (s.precomposeSliceEdge p).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_sourceEvaluation]
  exact s.precomposeSliceEdge_projection p

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeSquareEdge_source)


/-- 始点を前合成する四角形比較の終点成分は定値辺。 -/
lemma precomposeSquareEdge_target (p : V ⟶ A) :
    ((s.precomposeSquareEdge p).map ((truncation 2).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)))).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square).app (Opposite.op ⦋0⦌)
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cospanTargetVertex) 1 := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan s.square) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])) 1 1)).app _
        (s.precomposeSliceEdge p).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.sliceSquareDiagramMap_targetEvaluation]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (precomposeSquareEdge_target)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
