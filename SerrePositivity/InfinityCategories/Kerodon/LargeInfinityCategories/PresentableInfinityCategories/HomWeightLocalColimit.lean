module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightElementsComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.PresheafDensity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：任意の関手の局所左 Kan 形状上の Yoneda 図式に、元の Hom 前層を頂点とする余極限を作る。
方針：元の Hom 前層の密度余錐を、射影を厳密に保つ比較同値で制限する。
規約：指定単位から誘導される余錐との比較は別工程。
使われ方：P-12 の Hom 係数族の左 Kan 普遍性を点ごとの密度へ還元する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


local instance supplyHomWeightLocalColimit_projectionRightFibration
    {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.pullback_fst _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm c)))⟩

local instance supplyHomWeightLocalColimit_shapeQuasicategory
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c) :=
  quasicategory_of_innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c)

/-- 概要：元の局所左 Kan 形状上で A の元の Yoneda 図式を固定する。
方針：同じ元の射影だけを宇宙変更して Yoneda へ合成する。
規約：形状は任意の F の slice 引き戻し。使われ方：Hom 前層の局所密度表示。 -/
def homWeightLocalYonedaDiagram {A C : SSet.{u}} [Quasicategory A]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape F c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A :=
  (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection F c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A

/-- 概要：元の密度図式の実比較への制限は局所 Yoneda 図式そのもの。
方針：比較の厳密な射影則を持ち上げる。
規約：全図式の等式。使われ方：元の密度全余錐の型の正規化。 -/
lemma homWeightLocalElementsComparison_yoneda
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison F c) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c) = homWeightLocalYonedaDiagram F c := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafElementsYonedaDiagram, ← Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison_projection]
  rfl

/-- 概要：元の Hom 前層の密度全余錐を局所左 Kan 形状へ制限する。
方針：射影を保つ実比較で元の全余錐を制限し、図式の厳密な一致を使う。
規約：元の全余錐写像を保持する。使われ方：Hom 係数族の点ごとの余極限の指定。 -/
def homWeightLocalYonedaCocone
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (homWeightLocalYonedaDiagram F c) :=
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c)).restrict
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison F c))
  ⟨d.val, d.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison_yoneda F c)⟩

/-- 概要：局所 Yoneda 全余錐の頂点は元の Hom 前層そのもの。
方針：join の制限が右の零単体を固定することと元の密度頂点の式を使う。
規約：頂点の同型ではなく等式。使われ方：Hom 係数族の元の値の回収。 -/
lemma homWeightLocalYonedaCocone_vertex
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) :
    (homWeightLocalYonedaCocone F c).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison F c))
      (𝟙 (Δ[0] : SSet.{u + 1})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c)).val)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone_vertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c)

/-- 概要：元の Hom 前層を頂点とする局所 Yoneda 全余錐は余極限。
方針：元の密度余極限を実比較の同値で制限して普遍性を保存する。
規約：F の充満忠実性や C の余完備性は要求しない。
使われ方：指定単位の左 Kan 普遍性を検証するための局所余極限。 -/
lemma homWeightLocalYonedaCocone_isColimit
    {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (c : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (homWeightLocalYonedaCocone F c) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison F c))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison_isPrecompositionEquivalence F c).isQCatEquivalence)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c))).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.Cocompletion.presheafDensityCocone_isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightPresheaf F c)).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalElementsComparison F c)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightLocalYonedaCocone F c) rfl).mp h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
