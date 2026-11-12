module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentablePresheafSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ClassificationTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.QCatEquivalenceOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Shapes
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafHomWeights
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafUnstraightening

/-!
概要：任意の関手の局所左 Kan 形状を、元の Hom 係数前層の元の圏へ比較する。
方針：slice 引き戻しの反転を分類し、実際の復元射を元の宇宙へ反転して戻す。
規約：元の A への射影を厳密に保つ比較射を構成する。
使われ方：P-12 の Yoneda 指定単位の局所普遍性を密度余極限で検査する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


local instance supplyHomWeightElementsComparison_opEquivalence
    : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

local instance supplyHomWeightElementsComparison_projectionRightFibration
    {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))⟩

/-- 概要：元の Hom_C(F(-),c) を一つの元の空間値前層として固定する。
方針：同じ元の表現可能前層を F の反転で制限する。
規約：宇宙は元の A・C の宇宙。使われ方：局所左 Kan 形状の密度模型。 -/
def homWeightPresheaf {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C)
    (c : C _⦋0⦌) : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity c

/-- 概要：局所左 Kan 射影の反転の分類は元の Hom 係数前層と同型。
方針：引き戻し正方形を反転し、分類の底変換と表現可能 slice 比較を合成する。
規約：元の局所形状の射影を使う。使われ方：小さい復元射の標的の指定。 -/
def homWeightLocalProjection_classificationIso
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c)))
      (homWeightPresheaf F c) := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)
  let k := SSet.opFunctor.map F
  let r := SSet.opFunctor.map q
  have hs := ((IsPullback.of_hasPullback F q).map SSet.opFunctor).flip
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd r k) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd r k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := r))⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.leftClassification_overIso (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c))
    (pullback.snd r k) hs.isoPullback hs.isoPullback_hom_snd ≪≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso r k).symm ≪≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity_sliceIso c).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map k)).symm

/-- 概要：反転した局所形状から指定 Hom 前層の小さい left unstraightening への射。
方針：同じ分類の復元射と前層の分類同型に沿う小さい比較を合成する。
規約：底は A.op。使われ方：元の圏への比較を反転前の模型で固定する。 -/
def homWeightLocalOppositeComparison
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (homWeightPresheaf F c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso (homWeightLocalProjection_classificationIso F c)

/-- 概要：反転模型の比較は元の射影を厳密に保つ。
方針：復元と分類同型の小さい比較の射影則を合成する。
規約：底の射は恒等。使われ方：元の圏の比較の射影の回収。 -/
lemma homWeightLocalOppositeComparison_projection
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    homWeightLocalOppositeComparison F c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (homWeightPresheaf F c) =
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c) := by
  rw [homWeightLocalOppositeComparison, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_projection]

/-- 概要：反転模型の比較は元の全空間上の前合成同値。
方針：復元と前層同型の二つの同値性を合成する。
規約：実際の比較射を保持する。使われ方：密度余極限の形状置換。 -/
lemma homWeightLocalOppositeComparison_isPrecompositionEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (homWeightLocalOppositeComparison F c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_isPrecompositionEquivalence _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence _)

/-- 概要：元の局所左 Kan 形状から元の Hom 前層の元の圏への実比較。
方針：反転模型の比較を反転し、元の全空間の二重反転を戻す。
規約：元の小さい形状を使う。使われ方：同じ表現可能図式の密度表示。 -/
def homWeightLocalElementsComparison
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening (homWeightPresheaf F c) :=
  (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).inv ≫
    SSet.opFunctor.map (homWeightLocalOppositeComparison F c)

/-- 概要：元の元の圏への比較は A への射影を厳密に保つ。
方針：反転前の射影則と二重反転の自然性を計算する。
規約：図式の同型への弱化は不要。使われ方：元の Yoneda 密度図式の制限。 -/
lemma homWeightLocalElementsComparison_projection
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    homWeightLocalElementsComparison F c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection (homWeightPresheaf F c) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c := by
  unfold homWeightLocalElementsComparison _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection
  calc
    _ = (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).inv ≫
        SSet.opFunctor.map (homWeightLocalOppositeComparison F c ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningProjection (homWeightPresheaf F c)) ≫
        (SSet.opFunctorCompOpFunctorIso.app A).hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c)) ≫
        (SSet.opFunctorCompOpFunctorIso.app A).hom := by
      rw [homWeightLocalOppositeComparison_projection]
    _ = (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).inv ≫
        (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c := by
      exact congrArg (fun t ↦
        (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).inv ≫ t)
        (SSet.opFunctorCompOpFunctorIso.hom.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c))
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c := by
      rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 概要：元の局所左 Kan 形状と元の Hom 前層の元の圏の実比較は前合成同値。
方針：反転前の同値を反転して二重反転の同型を合成する。
規約：小さい元の全空間の射を判定する。使われ方：密度余極限を局所 Kan 形状へ制限。 -/
lemma homWeightLocalElementsComparison_isPrecompositionEquivalence
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (homWeightLocalElementsComparison F c) := by
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c) :=
    quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c)).symm).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_op
        (homWeightLocalOppositeComparison_isPrecompositionEquivalence F c).isQCatEquivalence
        |>.isPrecompositionEquivalence)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
