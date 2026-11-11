module
public import SerrePositivity.KST.SConstruction.TracedBFSpectrumCompositionEdge
public import SerrePositivity.KST.SConstruction.EnrichedCompositionReplacement

/-! # 元の BF 比較面を保持する coherent な入力二射の合成面
概要：元の BF 境界比較円柱を全比較面として保持した実四面体と合成三角形を構成する。
方針：同じ比較辺を coherent Hom に写し、標準合成面と共通の恒等面を持つ内ホーンを充填する。
規約：元の全比較面を保持する。三射以上の共有面の整合性はこの構成だけからは主張しない。
使われ方：BF スペクトル値の coherent 関手化の二単体工程。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance tracedCoherentSpectrumSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance tracedCoherentSpectrumQuasicategory :
    Quasicategory (SimplicialNerve OmegaSpectrum.{u}) := sp_quasicategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 境界円柱の全比較面と標準合成面を同時に持つ同じ実四面体。 -/
def monicKTracedCoherentCompositionData :=
  enrichedCompositionReplacement (monicKTracedSpectrumMap F f)
    (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F (f ≫ g))
    (monicKTracedSpectrumCompositionEdge F f g)

/-- 元の BF 境界射二つと合成入力の同じ BF 境界射を結ぶ実合成三角形。 -/
def monicKTracedCoherentComposition : SSet.Edge.CompStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F f))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F g))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (monicKTracedSpectrumMap F (f ≫ g))) :=
  (monicKTracedCoherentCompositionData F f g).triangle

/-- 新しい合成面は同じ四面体の第一面そのもの。 -/
lemma monicKTracedCoherentComposition_face :
    (monicKTracedCoherentComposition F f g).simplex =
      (SimplicialNerve OmegaSpectrum.{u}).δ 1
        (monicKTracedCoherentCompositionData F f g).simplex :=
  (monicKTracedCoherentCompositionData F f g).triangle_face

/-- 元の BF 比較円柱を写した全 pinched 比較面を厳密に保持する。 -/
lemma monicKTracedCoherentComposition_comparison_face :
    (SimplicialNerve OmegaSpectrum.{u}).δ 2
        (monicKTracedCoherentCompositionData F f g).simplex =
      (enrichedComparisonPinchedEdge (monicKTracedSpectrumCompositionEdge F f g)).edge.val :=
  (monicKTracedCoherentCompositionData F f g).replacement_face.trans
    (enrichedComparisonPinchedTriangle_simplex _)

/-- 元の二つの通常射の標準合成面も同じ四面体の面として厳密に保持する。 -/
lemma monicKTracedCoherentComposition_original_face :
    (SimplicialNerve OmegaSpectrum.{u}).δ 0
        (monicKTracedCoherentCompositionData F f g).simplex =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct (monicKTracedSpectrumMap F f)
        (monicKTracedSpectrumMap F g)).simplex :=
  (monicKTracedCoherentCompositionData F f g).original_face

end SerrePositivity.KST.SConstruction
