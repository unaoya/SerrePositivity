module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndDensityCocone
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.NativeFilteredPreservation

/-!
概要：Indκ の指定頂点そのものを持つ、元の小さい元の圏上の κ-filtered 密度余錐。
方針：元の前層頂点を関手へ戻し、同じ密度余錐の頂点を全部分包含の単射性で同定する。
規約：元の頂点と元の全余錐を保つ。対象ごとに同値な別表示を選び直さない。
使われ方：保存関手の値と、Yoneda による制限の可逆性の検出。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌)

/-- 元の Indκ 頂点が表す、同じ前層の実際の関手。 -/
def indVertexPresheaf : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).symm v.val

lemma indVertexPresheaf_vertex : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (indVertexPresheaf κ v) = v.val :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinityObjectEquiv C).apply_symm_apply v.val

lemma indVertexPresheaf_mem : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ C (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (indVertexPresheaf κ v)) :=
  (indVertexPresheaf_vertex κ v).symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v

/-- 同じ指定 Indκ 頂点の元の元の圏上の密度余錐。 -/
def indVertexDensityCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indDensityDiagram κ (indVertexPresheaf κ v)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indDensityCocone κ (indVertexPresheaf κ v) (indVertexPresheaf_mem κ v)

lemma indVertexDensityCocone_vertex : (indVertexDensityCocone κ v).vertex = v := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indDensityCocone_vertex κ (indVertexPresheaf κ v)
    (indVertexPresheaf_mem κ v)).trans (indVertexPresheaf_vertex κ v)

lemma indVertexDensityCocone_isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (indVertexDensityCocone κ v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indDensityCocone_isColimit κ (indVertexPresheaf κ v) (indVertexPresheaf_mem κ v)

/-- 同じ指定頂点の元の元の圏は小さい κ-filtered ∞ 圏。 -/
lemma indVertexElements_isKappaFiltered [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening (indVertexPresheaf κ v)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_functorVertex_iff κ C _).mp (indVertexPresheaf_mem κ v)

/-- 保存関手による元の全密度余錐の像は、同じ指定値の native 余極限。 -/
lemma indVertexDensity_image_isColimit [Fact κ.IsRegular] {D : SSet.{u + 1}}
    (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C ⟶ D) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesSmallKappaFilteredColimits κ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (indVertexDensityCocone κ v)) := by
  have := indVertexElements_isKappaFiltered κ v
  exact hG _ _ _ (indVertexDensityCocone_isColimit κ v)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
