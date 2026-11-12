module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteLeftFibrationCompact
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.FixedVertexMapSmallness

/-!
概要：一般の小さい ∞ 圏上の前層の、小さい compact 全部分生成圏を構成する。
方針：有限底上符号族と元の全表示を分類同値で送り、小さい全部分模型へ移す。
規約：生成圏と filtered 添字は宇宙 u、前層は u+1。各指定前層を厳密な頂点にする。
使われ方：前層の accessibility と presentable 性。

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

variable (C : SSet.{u}) [Quasicategory C]

omit [Quasicategory C] in
/-- 概要：元の前層 ∞ 圏では頂点を固定した小さい始域の全写像の型が小さい。
方針：空間の同じ性質を小さい底の内部 Hom へ移す。
規約：実際の全写像の小ささを述べ、局所小ささを追加仮定にしない。
使われ方：小さい compact 全部分模型の構成。 -/
lemma presheaf_hasSmallFixedVertexMaps : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) := by
  have (n : SimplexCategoryᵒᵖ) :
      Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj C.op).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1, u} (C.op.obj n)))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.space_hasSmallFixedVertexMaps.functorSpace
    ((SSet.uliftFunctor.{u + 1, u}).obj C.op)

/-- 概要：共通の有限底上符号族を元の前層の頂点族へ分類する。
方針：反転した底上の連続置換に同じ straightening を適用する。
規約：符号型は宇宙 u の FiniteOverCode C.op。
使われ方：小さい compact 全部分生成圏の対象族。 -/
def finitePresheafGeneratorVertex (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverCode C.op) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityMap C.op).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationGeneratorVertex q)

/-- 概要：分類した同じ小さい有限符号族の全項は compact である。
方針：元の left fibration の compact 性を同じ分類同値で輸送する。
規約：元の全 Hom による compact 性の定義を使う。
使われ方：小さい生成圏の compact 性。 -/
lemma finitePresheafGeneratorVertex_isCompact (q : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverCode C.op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} Cardinal.aleph0 (finitePresheafGeneratorVertex C q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_image_of_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityEquivalence C.op) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationGeneratorVertex_isCompact q)

/-- 概要：元の前層の共通の小さい compact 族を全部分圏として縮小する。
方針：頂点を固定した全写像の小ささで全次数を宇宙 u へ戻す。
規約：元の前層への全部分包含を保持する。
使われ方：accessibility に用いる小さい生成圏。 -/
def presheafCompactGeneratorCategory : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)

/-- 概要：縮小した同じ compact 生成圏は quasicategory である。
方針：小さい全部分模型の既存のホーン充填を用いる。
規約：元の前層と同じ頂点族を用いる。
使われ方：accessibility の小さい生成圏の充填性。 -/
instance presheafCompactGeneratorCategory_quasicategory :
    Quasicategory (presheafCompactGeneratorCategory C) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel
    (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)))

/-- 概要：元の前層 ∞ 圏への、同じ小さい compact 全部分模型の包含。
方針：縮小同型と元の全部分包含を合成する。
規約：対象だけでなく全写像空間の包含を保持する。
使われ方：前層の compact 生成性の公開界面。 -/
def presheafCompactGeneratorInclusion :
    (SSet.uliftFunctor.{u + 1, u}).obj (presheafCompactGeneratorCategory C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)

/-- 概要：同じ小さい全部分模型は元の任意の前層を compact 生成する。
方針：有限底上模型の全表示を分類し、元の前層を厳密な頂点として回収する。
規約：同型飽和内の全図式を一つの小さい全部分圏へ移す。
使われ方：一般の前層の ℵ₀-accessibility。 -/
lemma presheafCompactGeneratorInclusion_isCompactGenerating :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating Cardinal.aleph0 (presheafCompactGeneratorInclusion C) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isKappaCompactGenerating
    (presheaf_hasSmallFixedVertexMaps C) (finitePresheafGeneratorVertex C)
    (finitePresheafGeneratorVertex_isCompact C)
  intro x
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityEquivalence C.op
  let y := e.inv.app (Opposite.op ⦋0⦌) x
  let X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y
  obtain ⟨d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_finiteLeftFibrationPresentation X
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationDiagram X.val) ≫ e.hom
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone e.hom d
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence d).mp hd
  have hcv : c.vertex = e.hom.app (Opposite.op ⦋0⦌) y := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hv]
    exact congrArg (e.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y)
  obtain ⟨c', hc', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso c hc
    (eqToIso (congrArg HomotopyCategory.mk hcv) ≪≫ e.invHomIso.app x)
  refine ⟨nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.FiniteOverPieces X.val), inferInstance,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteOverPresentation.finiteOverPieces_nerve_isKappaFiltered X.val, G, ?_, c', hc', hv'⟩
  intro a
  obtain ⟨q, ⟨hq⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteLeftFibrationDiagram_in_family X.val a
  exact ⟨q, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map hq e.hom⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
