module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：反変重みの自然変換が coend に誘導する射と、その添字変更との整合。
方針：各脚の重みの変数に自然変換を作用させる。
規約：図式の係数は固定する。
使われ方：Bousfield–Kan 重みの添字関手に沿う比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I J : Type u} [SmallCategory I] [SmallCategory J]

/-- 概要：重みの自然変換から coend の射を構成する。
方針：各脚で重みの変数だけを写す。
規約：図式の対象と構造射は固定。使われ方：coend の重みの変更。 -/
def weightedColimitWeightMap {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V) (F : I ⥤ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit V F :=
  coend.desc (fun i ↦ (F.obj i ◁ μ.app (Opposite.op i)) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι V F i) (by
    intro i j f
    change (F.obj i ◁ W.map f.op) ≫ (F.obj i ◁ μ.app (Opposite.op i)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι V F i =
        (F.map f ▷ W.obj (Opposite.op j)) ≫ (F.obj j ◁ μ.app (Opposite.op j)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι V F j
    rw [← whiskerLeft_comp_assoc, μ.naturality f.op, whiskerLeft_comp_assoc,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition, whisker_exchange_assoc])

/-- 概要：重みの変更の各脚での計算。
方針：coend の降下の計算則。
規約：単体集合の射の厳密な等式。使われ方：重み変更の合成則。 -/
lemma weightedColimitι_weightMap {W V : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V)
    (F : I ⥤ SSet.{u}) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ≫ weightedColimitWeightMap μ F =
      (F.obj i ◁ μ.app (Opposite.op i)) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι V F i := coend.ι_desc _ _ i

/-- 概要：恒等な重み変更は coend の恒等射。
方針：普遍脚上で直積の恒等を計算する。
規約：元の coend を保持する。使われ方：添字変更の単位則。 -/
lemma weightedColimitWeightMap_id (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    weightedColimitWeightMap (𝟙 W) F = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro i
  rw [weightedColimitι_weightMap]
  simp only [NatTrans.id_app, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- 概要：重み変更の二段の合成は自然変換の合成による変更。
方針：普遍脚と tensor の合成則を比較する。
規約：元の図式 F は同じ。使われ方：coend の関手性。 -/
lemma weightedColimitWeightMap_comp {W V T : Iᵒᵖ ⥤ SSet.{u}} (μ : W ⟶ V) (ν : V ⟶ T)
    (F : I ⥤ SSet.{u}) :
    weightedColimitWeightMap μ F ≫ weightedColimitWeightMap ν F =
      weightedColimitWeightMap (μ ≫ ν) F := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro i
  rw [reassoc_of% weightedColimitι_weightMap, weightedColimitι_weightMap,
    weightedColimitι_weightMap]
  simp only [NatTrans.comp_app, whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
