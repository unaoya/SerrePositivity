module

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanDiagrams
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows

/-!
概要：反転関手で写した分母付き span を、元の両端点を保つ実三角形とその第三辺へ評価する。
方針：可逆 span の三角形補完射影を基底変更し、その厳密切断を選ぶ。
規約：補完射影は全境界を持ち上げる。写像空間との同値性は後続。
使われ方：局所化後の分数の評価と指定端点を持つ族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W)

def fractionTriangleDiagrams : SSet.{u} :=
  pullback (equivalenceSpanTriangleProjection Q) (invertedSpanMap F W hF)

def fractionTriangleProjection : fractionTriangleDiagrams F W hF ⟶ markedSpans X W :=
  pullback.snd _ _

instance fractionTriangleProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (fractionTriangleProjection F W hF) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

def fractionTriangleFamily : fractionTriangleDiagrams F W hF ⟶ (ihom (Δ[2] : SSet.{u})).obj Q :=
  pullback.fst (equivalenceSpanTriangleProjection Q) (invertedSpanMap F W hF) ≫
    pullback.fst ((pre (horn 2 0).ι).app Q) (equivalenceSpanInclusion Q)

omit [Quasicategory Q] in
lemma fractionTriangleFamily_span : fractionTriangleFamily F W hF ≫
    (pre (horn 2 0).ι).app Q = fractionTriangleProjection F W hF ≫
      markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F := by
  rw [fractionTriangleFamily, Category.assoc, pullback.condition, ← Category.assoc]
  change (pullback.fst _ _ ≫ equivalenceSpanTriangleProjection Q) ≫
    equivalenceSpanInclusion Q = _
  rw [pullback.condition, Category.assoc, invertedSpanMap_inclusion]
  rfl

def fractionTriangleSection : markedSpans X W ⟶ fractionTriangleDiagrams F W hF :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (fractionTriangleProjection F W hF))

lemma fractionTriangleSection_projection :
    fractionTriangleSection F W hF ≫ fractionTriangleProjection F W hF = 𝟙 _ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (fractionTriangleProjection F W hF))

lemma exists_relative_fractionTriangleFamily {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (d : B ⟶ markedSpans X W) (a : A ⟶ fractionTriangleDiagrams F W hF)
    (ha : a ≫ fractionTriangleProjection F W hF = i ≫ d) :
    ∃ G : B ⟶ fractionTriangleDiagrams F W hF,
      i ≫ G = a ∧ G ≫ fractionTriangleProjection F W hF = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := fractionTriangleProjection F W hF) i inferInstance
  have sq : CommSq a i (fractionTriangleProjection F W hF) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

def fractionTriangleFamilySpace {B : SSet.{u}} (d : B ⟶ markedSpans X W) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom B).map (fractionTriangleProjection F W hF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

lemma fractionTriangleFamilySpace_isContractibleKan {B : SSet.{u}} (d : B ⟶ markedSpans X W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (fractionTriangleFamilySpace F W hF d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan ((ihom B).map (fractionTriangleProjection F W hF)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

def fractionEvaluationTriangle : markedSpans X W ⟶ (ihom (Δ[2] : SSet.{u})).obj Q :=
  fractionTriangleSection F W hF ≫ fractionTriangleFamily F W hF

lemma fractionEvaluationTriangle_span : fractionEvaluationTriangle F W hF ≫
    (pre (horn 2 0).ι).app Q =
      markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F := by
  rw [fractionEvaluationTriangle, Category.assoc, fractionTriangleFamily_span,
    ← Category.assoc, fractionTriangleSection_projection, Category.id_comp]

def fractionSpanEvaluation : markedSpans X W ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
  fractionEvaluationTriangle F W hF ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q

lemma fractionSpanEvaluation_source : fractionSpanEvaluation F W hF ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      (markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F) ≫
        (pre horn₂₀.ι₀₁).app Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [← fractionEvaluationTriangle_span F W hF]
  change (fractionEvaluationTriangle F W hF ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

lemma fractionSpanEvaluation_target : fractionSpanEvaluation F W hF ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      (markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F) ≫
        (pre horn₂₀.ι₀₂).app Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [← fractionEvaluationTriangle_span F W hF]
  change (fractionEvaluationTriangle F W hF ≫ (pre (stdSimplex.δ (0 : Fin 3))).app Q) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

end SerrePositivity.KST.LocalizingInvariants
