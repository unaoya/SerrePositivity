module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy

/-!
概要：連続 Kan 単位の図式全体での比較と、その filtered 余極限の弱同値性。
方針：単位の自然性と、Q の filtered 余極限保存の標準同型を使う。
規約：元の図式の値の Kan 性は不要。
使われ方：任意の単体集合値の filtered 図式を Kan 値図式に移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I]

/-- 概要：元の図式から Q を点ごとに適用した図式への単位自然変換。
方針：Q の単位を元の図式で前合成する。
規約：元の図式全体で自然。使われ方：成分ごとの置換を余極限で比較する。 -/
def continuousKanDiagramUnit (F : I ⥤ SSet.{u}) : F ⟶ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement :=
  Functor.whiskerLeft F _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit

/-- 概要：単位の余極限は Q の colimit 保存同型の下で colimit 自体の単位に一致する。
方針：各余極限の脚で保存同型と単位の自然性を使う。
規約：同型は選ばれた実際の保存同型。使われ方：余極限の単位の弱同値性。 -/
lemma continuousKanDiagramUnit_colimit_factor [IsFiltered I] (F : I ⥤ SSet.{u}) :
    colim.map (continuousKanDiagramUnit F) ≫ (preservesColimitIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement F).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (colimit F) := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, colimit.ι_map, Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (F.obj i) ≫
    colimit.ι (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement) i ≫
      (preservesColimitIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement F).inv =
        colimit.ι F i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (colimit F)
  rw [ι_preservesColimitIso_inv]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality (colimit.ι F i)).symm

/-- 概要：点ごとの Kan 単位の filtered 余極限も弱ホモトピー同値。
方針：保存同型の弱同値性を消去して、colimit の単位の弱同値性へ帰着する。
規約：元の図式は任意の単体集合値。使われ方：filtered 余極限の Kan 模型比較。 -/
lemma continuousKanDiagramUnit_colimit_isWeakHomotopyEquivalence [IsFiltered I]
    (F : I ⥤ SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map (continuousKanDiagramUnit F)) := by
  let e := (preservesColimitIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement F).symm
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e).isWeakHomotopyEquivalence
  apply he.cancel_right
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (colim.map (continuousKanDiagramUnit F) ≫
    (preservesColimitIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement F).inv)
  rw [continuousKanDiagramUnit_colimit_factor]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
