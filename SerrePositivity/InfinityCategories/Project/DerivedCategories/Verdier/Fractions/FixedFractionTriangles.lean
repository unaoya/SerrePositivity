module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionMappingComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionEvaluation

/-!
概要：両端固定の分数に実三角補完を記憶させても、その亜群化は変わらない。
方針：分数三角補完の射影を固定端点 span に基底変更し、実切断と逆比較を保持する。
規約：補完を忘れる射影自体を順方向に持つ同値。分数評価の同値性は未証明。
使われ方：局所化の写像空間比較を相対 Ore 補完で計算する際の模型変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (x y : X _⦋0⦌)

def fixedFractionTriangles : SSet.{u} :=
  pullback (fractionTriangleProjection F W hF) (fixedMarkedSpanInclusion X W x y)

def fixedFractionTriangleProjection : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x y ⟶
    fixedMarkedSpans X W x y := pullback.snd _ _

instance fixedFractionTriangleProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

def fixedFractionTriangleSection : fixedMarkedSpans X W x y ⟶
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x y :=
  pullback.lift (fixedMarkedSpanInclusion X W x y ≫ fractionTriangleSection F W hF)
    (𝟙 _) (by rw [Category.assoc, fractionTriangleSection_projection, Category.comp_id,
      Category.id_comp])

lemma fixedFractionTriangleSection_projection :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleSection F W hF x y ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y =
      𝟙 _ := pullback.lift_snd _ _ _

def fixedFractionTriangleFamily : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x y ⟶
    (ihom (Δ[2] : SSet.{u})).obj Q :=
  pullback.fst (fractionTriangleProjection F W hF) (fixedMarkedSpanInclusion X W x y) ≫
    fractionTriangleFamily F W hF

omit [Quasicategory Q] in
lemma fixedFractionTriangleFamily_span : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily F W hF x y ≫
    (pre (horn 2 0).ι).app Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫
      fixedMarkedSpanInclusion X W x y ≫ markedSpanInclusion X W ≫
        (ihom (horn 2 0 : SSet.{u})).map F := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily, Category.assoc, fractionTriangleFamily_span,
    ← Category.assoc, ← Category.assoc, pullback.condition]
  rfl

lemma fixedFractionTriangleSection_family : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleSection F W hF x y ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily F W hF x y =
      fixedMarkedSpanInclusion X W x y ≫ fractionEvaluationTriangle F W hF := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleFamily, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.fst _ _) ≫ _ = _
  rw [pullback.lift_fst, Category.assoc]
  rfl

def fixedFractionTriangleCompletionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangles F W hF x y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans X W x y)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfTrivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y)

lemma fixedFractionTriangleEvaluation_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEvaluation
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y ≫ fixedFractionPinchedEvaluation F W hF x y)) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionPinchedMappingComparison F W hF x y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEvaluation_trivialKanFibration_iff
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fixedFractionTriangleProjection F W hF x y) (fixedFractionPinchedEvaluation F W hF x y)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
