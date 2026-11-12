module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedColimit

/-!
概要：添字関手に沿って制限した重み付き coend から元の coend への標準射。
方針：元の coend の脚を添字関手の像で評価して降下させる。
規約：cofinality・Kan 性・filtered 性を定義に要求しない。
使われ方：Over.map に沿う Bousfield–Kan coend の図式。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I J K : Type u} [SmallCategory I] [SmallCategory J] [SmallCategory K]

/-- 概要：制限した図式と重みの coend を元の coend へ送る。
方針：U の像での普遍脚を使う。
規約：重みは反変、図式は共変。使われ方：coend の添字変更。 -/
def weightedColimitReindex (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (U : J ⥤ I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit (U.op ⋙ W) (U ⋙ F) ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F :=
  coend.desc (fun j ↦ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F (U.obj j)) (by
    intro i j f
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition W F (U.map f))

/-- 概要：添字変更は各脚を元の図式の像の脚へ送る。
方針：coend の降下の計算則。
規約：厳密な射の等式。使われ方：添字変更の合成則。 -/
lemma weightedColimitι_reindex (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (U : J ⥤ I)
    (j : J) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι (U.op ⋙ W) (U ⋙ F) j ≫ weightedColimitReindex W F U =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F (U.obj j) := coend.ι_desc _ _ j

/-- 概要：恒等関手による添字変更は恒等射。
方針：全ての普遍脚で比較する。
規約：重みと図式を変更しない。使われ方：添字変更の単位則。 -/
lemma weightedColimitReindex_id (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    weightedColimitReindex W F (𝟭 I) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro i
  rw [weightedColimitι_reindex]
  change _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i = _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ≫ 𝟙 _
  rw [Category.comp_id]

/-- 概要：二段の添字変更は合成関手による添字変更に等しい。
方針：各脚を順に像の脚へ移す。
規約：合成の向きは V の後に U。使われ方：Over の構造射の関手性。 -/
lemma weightedColimitReindex_comp (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (U : J ⥤ I) (V : K ⥤ J) :
    weightedColimitReindex (U.op ⋙ W) (U ⋙ F) V ≫ weightedColimitReindex W F U =
      weightedColimitReindex W F (V ⋙ U) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_hom_ext
  intro k
  rw [reassoc_of% weightedColimitι_reindex, weightedColimitι_reindex]
  exact (weightedColimitι_reindex W F (V ⋙ U) k).symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
