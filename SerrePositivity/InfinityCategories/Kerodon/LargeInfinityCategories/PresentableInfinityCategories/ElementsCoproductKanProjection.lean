module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductLeftKan

/-!
概要：要素圏の局所左 Kan 比較が保つ元の全射影。
方針：comma の nerve 比較と宇宙比較の射影公式を合成する。
規約：対象ごとの同値だけでなく図式の等式を与える。
使われ方：有限段の余積存在を全局所左 Kan 図式へ渡す。

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

/-- 概要：離散ファイバー比較は元の要素圏への全射影を保つ。
方針：二つの指定比較の射影を順に正規化する。
規約：元の次数と要素を保持する。
使われ方：任意の要素圏上の入力図式の制限。 -/
lemma elementsCoproductKanComparison_projection
    {I : Type u} [Category.{u} I] (Y : I ⥤ Type u) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Y i ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (Functor.Elements.π Y))) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y i ⋙ CostructuredArrow.proj _ i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso_projection, ← Functor.map_comp]
  apply congrArg (SSet.uliftFunctor.{u + 1, u}).map
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso_hom_projection]
  rfl

/-- 概要：各離散ファイバーの余極限だけから全局所左 Kan 余極限が存在する。
方針：元の全射影の等式とファイバー比較の cofinal 性を使う。
規約：標的の全小余積の存在は要求しない。
使われ方：表現可能対象の有限余積だけを使う構成。 -/
lemma elements_leftKanDiagram_hasColimit_of_fibers
    {I : Type u} [Category.{u} I] (Y : I ⥤ Type u)
    {X : SSet.{u + 1}} [Quasicategory X]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) ⟶ X)
    (h : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y i ⋙ CostructuredArrow.proj _ i)) ≫ F))
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F v) := by
  rcases v with ⟨v⟩
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison Y i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsCoproductKanComparison_isRightCofinal Y i)
  have he := congrArg (fun g ↦ g ≫ F) (elementsCoproductKanComparison_projection Y i)
  rw [Category.assoc] at he
  exact he.symm ▸ h i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
