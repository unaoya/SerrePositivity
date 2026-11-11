module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeUnstraighteningCommonPrism

/-!
概要：共通 weighted 係数上の全 Hom の作用を、元の係数の同時評価へ展開する。
方針：相対 Hom の宇宙移送と展開の可換性を先に示し、右端射影を保持する。
規約：全 Hom の Kan 性や通常の射への制限を要求しない。
使われ方：weighted 側の pointed prism の実際の終点を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors


/-- 相対射の族を宇宙移送して展開すると、元の展開の宇宙持ち上げに厳密に一致する。 -/
lemma uliftRelativeFunctorMap_uncurry {A E B T : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
      ((SSet.uliftFunctor.{v, u}).map f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftRelativeFunctorIso.{u, v} p a).hom) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso A T).inv ≫ (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f) := by
  apply SSet.hom_ext
  intro n
  rfl

variable {I : Type u} [SmallCategory I]

/-- 共通 Hom の weighted 作用は、右端射影に続く元の weighted 係数の全評価そのもの。 -/
lemma kanDiagramCommonWeightedAction_uncurry (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramCommonWeightedAction F G) =
    ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) ◁
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
      (SimplicialCategory.sHom F G)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramCommonWeightedAction, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality,
    uliftRelativeFunctorMap_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingSpaceMap_uncurry]

/-- 元の共通 weighted 始域から、元の標的 weighted nerve への全 Hom の評価。 -/
def strictKanCommonWeightedHomFamily (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanCommonWeightedParameterMap F.val ▷
    (SSet.uliftFunctor.{u + 1, u}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.kanDiagramCommonWeightedAction F G)

/-- 共通始域上の同時評価は、係数の射と Hom の右端射影をともに保持する。 -/
lemma strictKanCommonWeightedHomFamily_evaluation (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    strictKanCommonWeightedHomFamily F G =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanCommonWeightedParameterMap F.val ⊗ₘ
      (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight (SimplicialCategory.sHom F G))) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget))
      (SimplicialCategory.sHom F G)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveMappingFamily (F.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) := by
  rw [strictKanCommonWeightedHomFamily, kanDiagramCommonWeightedAction_uncurry,
    ← Category.assoc]
  congr 1

/-- 同時評価は共通 weighted 始域の底を保ち、Hom のパラメーターを底では忘れる。 -/
lemma strictKanCommonWeightedHomFamily_projection (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    strictKanCommonWeightedHomFamily F G ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (G.val ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) =
    fst _ _ ≫ (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanCommonDiagram F.val) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewisePointKanObject ⋙
        SSet.opFunctor)) := by
  rw [strictKanCommonWeightedHomFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
    whiskerRight_fst_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanCommonWeightedParameterMap_projection]

/-- weighted 側の終点は、同時評価の後に元の標的比較を続けた同じ相対射の族。 -/
lemma oppositeUnstraighteningHomLeft_common_uncurry (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictKanCommonWeightedParameterMap F.val ▷
      (SSet.uliftFunctor.{u + 1, u}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeUnstraighteningHomLeft F G) =
    strictKanCommonWeightedHomFamily F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.oppositeKanUnstraighteningComparison G.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeUnstraighteningHomLeft_uncurry, strictKanCommonWeightedHomFamily,
    Category.assoc]

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
