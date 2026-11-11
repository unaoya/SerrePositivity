module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SimplicialHomEnriched
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.FiniteInternalHomContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictCoconePostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FilteredKanCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality

/-!
概要：有限単体集合始点の全 Hom が、同じ strict filtered 余極限余錐を native に保存する。
方針：全豊穣作用の通常の作用を照合し、既存の有限内部 Hom の連続性を指定余錐像へ渡す。
規約：始点の Kan 性は要求しない。元の全脚と全単体を保持する。
使われ方：一般 coherent 図式での有限始点の filtered 保存。

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
lemma simplicialInternalHomEnriched_underlying (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched K) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomFunctor K := by
  refine CategoryTheory.Functor.ext
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched K))
    (G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomFunctor K) (fun _ ↦ rfl) ?_
  intro L M f
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched K)).map f =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomFunctor K).map f
  apply (SimplicialCategory.homEquiv'
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched K).obj L) ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomEnriched K).obj M)).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex]
  have ht : MonoidalClosed.curry' (C := SSet.{u}) f ≫
      MonoidalClosed.curry (MonoidalClosed.comp K L.obj M.obj) =
      MonoidalClosed.curry' ((ihom K).map f) := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    simp only [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
    exact MonoidalClosed.whiskerLeft_curry'_comp (C := SSet.{u}) f
  have hp := congrArg (fun q : (𝟙_ SSet.{u}) ⟶
      (ihom ((ihom K).obj L.obj)).obj
        ((ihom K).obj M.obj) ↦ SSet.unitHomEquiv _ q) ht
  exact hp

/-- 同じ全余錐への Hom 後合成は、元の通常の Hom 余錐の全単体と一致する。 -/
lemma simplicialInternalHom_strictCocone_postcomp_val (K : SSet.{u})
    {J : Type u} [SmallCategory J] {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (c : Cocone F) :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity K =
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomFunctor K).mapCocone c)).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictNativeCocone_postcomp_val,
    simplicialInternalHomEnriched_underlying]

/-- 有限始点からの全 Hom の像は、同じ filtered strict 全余錐の native な余極限である。 -/
lemma finiteSimplicialHomInfinity_preserves_strictCocone (K : SSet.{u}) [K.Finite]
    {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialInternalHomInfinity K) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.strictNativeCocone c)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _
    (simplicialInternalHom_strictCocone_postcomp_val K c)).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictNativeCocone_isColimit_of_filtered_forget
  exact isColimitOfPreserves (ihom K) hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
