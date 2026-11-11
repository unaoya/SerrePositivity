module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeParameterPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantTransformationNaturality

/-!
概要：native な終点固定余錐空間から、定値図式への変換空間への標準比較。
方針：元の余錐の全円柱を curry し、全パラメータで評価の一致を証明する。
規約：射の構成と同値性の証明を区別する。
使われ方：全空間の単位で構成した余錐の普遍性と後合成の整合の検証。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：native な余錐を元の図式から同じ定値頂点への変換にする。
方針：余錐の恒等族の円柱と、その厳密な両端条件を curry する。
規約：quasicategory 性は不要。使われ方：余錐の全 Hom と変換空間の比較。 -/
def coconeTransformationMap {K X : SSet.{u}} (f : K ⟶ X) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f z)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism_zero _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism_one _)

/-- 概要：比較射を適用した任意の族の円柱は、元の余錐の族の円柱そのもの。
方針：curry の往復と二つの円柱表示のパラメータ自然性を使う。
規約：全単体・全パラメータで厳密に一致。使われ方：後合成や単位との整合の検証。 -/
lemma coconeTransformationMap_prism {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace f z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism (a ≫ coconeTransformationMap f z) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism a := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_precomp, coconeTransformationMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantTransformationPrism_curry, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeParameterPrism_precomp, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
