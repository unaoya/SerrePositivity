module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeHomCoherentComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation

/-!
概要：coherent な Hom 関手間の変換を表現対象の恒等射で評価して回収する。
方針：表現対象で評価し、Kan 複体の coherent Hom 比較の逆を通して恒等射に作用させる。
規約：回収射は全写像空間に定義し、主比較との往復を実際の射で検証する。
使われ方：Hom の族の充満忠実性と、自然な全空間比較への回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 表現対象の恒等射で、相対 Hom 間の写像を評価する。 -/
def relativeHomIdentityEvaluation {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    SimplicialCategory.sHom
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).obj
        (Opposite.op q))
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).obj
        (Opposite.op a)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.unitHomEquiv _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val))

/-- 豊穣な前合成の作用を恒等射で評価すると、元の相対射の族そのもの。 -/
lemma relativeHomSourceEvaluationEnriched_identity {B : SSet.{u}}
    (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).map
      (Opposite.op q) (Opposite.op a) ≫ relativeHomIdentityEvaluation a q =
        𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q
  change F.map (Opposite.op q) (Opposite.op a) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (SSet.unitHomEquiv _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorIdentity q.val)) = _
  rw [← curry_uncurry (F.map (Opposite.op q) (Opposite.op a)),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.curry_evaluateFunctorAt_unitHomEquiv]
  change _ ≫ _ ≫ uncurry ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).map (Opposite.op q) (Opposite.op a)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched_map]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  exact congrArg (fun k ↦ k.app n f) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_id a.val q.val)

/-- 表現対象で評価した coherent 変換の写像空間を、実際の内部 Hom と比較する同値。 -/
def relativeHomIdentityCoherentEquivalence {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).obj
      (Opposite.op q))
    ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).obj
      (Opposite.op a))

/-- coherent な変換を表現対象の恒等射で評価し、相対 Hom の族へ回収する。 -/
def relativeHomCoherentRecovery {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation q.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation a.val)) ⟶
        (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom) :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentEvaluationMap a q q ≫
    (relativeHomIdentityCoherentEquivalence a q).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (relativeHomIdentityEvaluation a q)

/-- 主比較の後に恒等射で回収する往復は、相対 Hom 全体で恒等と関手同型。 -/
def relativeHomCoherentComparisonRecoveryIso {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison a q ≫ relativeHomCoherentRecovery a q)
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom))) := by
  let F := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q
  let U := SSet.uliftFunctor.{u + 1, u}
  let m := F.map (Opposite.op q) (Opposite.op a)
  let e := relativeHomIdentityCoherentEquivalence a q
  let v := relativeHomIdentityEvaluation a q
  have he : e.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (F.obj (Opposite.op q))
      (F.obj (Opposite.op a)) := rfl
  have hc : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison a q ≫ relativeHomCoherentRecovery a q =
      U.map m ≫ (e.hom ≫ e.inv) ≫ U.map v := by
    change (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison a q ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentEvaluationMap a q q) ≫
      e.inv ≫ U.map v = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison_evaluate, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_enriched_naturality]
    rw [he]
    rfl
  have hv : U.map m ≫ U.map v = 𝟙 (U.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom)) := by
    rw [← U.map_comp]
    change U.map ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomSourceEvaluationEnriched (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.leftFibrationOverEnriched B) q).map
      (Opposite.op q) (Opposite.op a) ≫ relativeHomIdentityEvaluation a q) = _
    rw [relativeHomSourceEvaluationEnriched_identity]
    exact U.map_id _
  have h := (e.homInvIso.precomp (U.map m)).postcomp (U.map v)
  rw [hc]
  simpa only [Category.assoc, Category.id_comp, hv] using h

/-- 主比較して回収する往復と恒等との、実際の単体的ホモトピー。 -/
def relativeHomCoherentComparisonRecoveryHomotopy {B : SSet.{u}}
    (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomCoherentComparison a q ≫ relativeHomCoherentRecovery a q)
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q.val.hom a.val.hom))) :=
  (relativeHomCoherentComparisonRecoveryIso a q).simplicialHomotopy

/-- coherent な変換を、全標的に自然な strict 比較空間へ回収する射。 -/
def relativeHomComparisonSpaceRecoveryMap {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation q.val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationCoherentEvaluation a.val)) ⟶
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpace a.val q :=
  relativeHomCoherentRecovery a q ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpaceIso a.val q).hom

/-- strict 比較空間から coherent な変換を経て回収する往復も恒等と関手同型。 -/
def relativeHomComparisonSpaceRecoveryIso {B : SSet.{u}} (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpaceCoherentMap a q ≫ relativeHomComparisonSpaceRecoveryMap a q)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpace a.val q)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpaceIso a.val q
  have h := ((relativeHomCoherentComparisonRecoveryIso a q).precomp e.inv).postcomp e.hom
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpaceCoherentMap, relativeHomComparisonSpaceRecoveryMap,
    Category.assoc, Category.id_comp, Category.comp_id, e.inv_hom_id] using h

/-- strict 比較空間での往復を恒等へ結ぶ単体的ホモトピー。 -/
def relativeHomComparisonSpaceRecoveryHomotopy {B : SSet.{u}}
    (a q : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpaceCoherentMap a q ≫ relativeHomComparisonSpaceRecoveryMap a q)
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeHomComparisonSpace a.val q)) :=
  (relativeHomComparisonSpaceRecoveryIso a q).simplicialHomotopy

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
