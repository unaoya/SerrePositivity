module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
概要：豊穣関手による coherent nerve の後合成。
方針：各 thickening からの豊穣関手に後合成し、面・退化との可換性を合成の結合性で示す。
規約：二つの単体的圏は Hom の宇宙 u、対象の宇宙 v を共有する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、豊穣評価から 𝒮 値の評価への移行。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：豊穣関手は coherent nerve の間の射を誘導する。
方針：各標準順序の thickening からの図式へ豊穣関手を後合成する。
規約：局所 Kan 性はこの構成自体には不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、単体的圏の評価を ∞ 圏の関手へ写す。 -/
def coherentNerveMap {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D] (F : EnrichedFunctor SSet.{u} C D) :
    SimplicialNerve C ⟶ SimplicialNerve D where
  app _ := ↾fun G ↦ G.comp SSet F
  naturality _ _ _ := rfl

/-- 概要：coherent nerve の後合成は恒等豊穣関手を恒等射へ写す。
方針：各図式の豊穣関手の恒等合成を計算する。
規約：単体的圏は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent nerve の関手性。 -/
lemma coherentNerveMap_id (C : Type v) [Category.{u} C] [SimplicialCategory C] :
    coherentNerveMap (EnrichedFunctor.id SSet.{u} C) = 𝟙 (SimplicialNerve C) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp

/-- 概要：coherent nerve の後合成は豊穣関手の合成を保つ。
方針：各単体で豊穣関手の三重合成を比較する。
規約：三つの単体的圏は同じ二つの宇宙を共有する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、評価と分類の合成の整合性。 -/
lemma coherentNerveMap_comp {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    [SimplicialCategory C] [SimplicialCategory D] [SimplicialCategory E]
    (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E) :
    coherentNerveMap (F.comp SSet G) = coherentNerveMap F ≫ coherentNerveMap G := rfl

/-- 概要：coherent nerve の射は各対象の標準頂点を像の対象の標準頂点へ写す。
方針：零単体の唯一の対象を計算し、coherent 頂点の復元の一意性を使う。
規約：対象 c の表示に選択した射は含めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、評価写像の対象での値の同定。 -/
lemma coherentNerveMap_vertex {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (c : C) :
    (coherentNerveMap F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (F.obj c) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((coherentNerveMap F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c))).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
