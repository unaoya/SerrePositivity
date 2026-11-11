module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallKanHomContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost

/-!
概要：小さい始点の全 Hom 関手が、strict 模型の同じ native 余極限余錐を保存する。
方針：豊穣関手の通常の作用を同定し、全 join 射の後合成公式で元の余錐へ戻す。
規約：元の全余錐の像を扱い、頂点だけの同値や射の成分ごとの選択を使わない。
使われ方：小さい空間の compact 性を一般 coherent 図式へ移すための native 界面。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 全豊穣内部 Hom の通常の作用は、元の strict 内部 Hom 関手そのもの。 -/
lemma kanInternalHomEnriched_underlying (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomEnriched K) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomFunctor K := by
  refine CategoryTheory.Functor.ext
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomEnriched K))
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomFunctor K) (fun _ ↦ rfl) ?_
  intro L M f
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomEnriched K)).map f =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomFunctor K).map f
  apply (SimplicialCategory.homEquiv'
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomEnriched K).obj L) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomEnriched K).obj M)).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex]
  have ht : MonoidalClosed.curry' (C := SSet.{u}) f ≫
      MonoidalClosed.curry (MonoidalClosed.comp K.obj L.obj M.obj) =
      MonoidalClosed.curry' ((ihom K.obj).map f) := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    simp only [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
    exact MonoidalClosed.whiskerLeft_curry'_comp (C := SSet.{u}) f
  have hp := congrArg (fun q : (𝟙_ SSet.{u}) ⟶
      (ihom ((ihom K.obj).obj L.obj)).obj
        ((ihom K.obj).obj M.obj) ↦ SSet.unitHomEquiv _ q) ht
  exact hp

/-- 同じ全余錐への Hom 後合成は、元の通常の Hom 余錐の全単体と一致する。 -/
lemma kanInternalHom_strictCocone_postcomp_val (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    {J : Type u} [SmallCategory J] {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cocone F) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomInfinity K =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomFunctor K).mapCocone c)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomInfinity, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictNativeCocone_postcomp_val,
    kanInternalHomEnriched_underlying]

/-- 元の全 Hom 関手の同じ余錐像が、μ-filtered strict Kan 余極限を native に保存する。 -/
lemma smallKanHomInfinity_preserves_strictCocone {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K.obj)
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J μ]
    {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cocone F) (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanInternalHomInfinity K) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _
    (kanInternalHom_strictCocone_postcomp_val K c)).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallKanHom_mapCocone_native hμ K hK c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
