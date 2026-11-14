module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitAugmentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitDegreeExt
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.WeightedColimitOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：coend の反転同型は通常の余極限への augmentation を保つ。
方針：反転した普遍脚で比較し、余極限保存同型の脚の式を使う。
規約：実際の標準比較射そのものの等式を示す。
使われ方：反転重みの filtered augmentation の弱同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

variable {I : Type u} [SmallCategory I]
local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：反転した coend からの射は反転した普遍脚で比較できる。
方針：各次数の評価で元の coend の外延性を使う。
規約：重みと係数は任意。使われ方：反転した augmentation の整合性。 -/
lemma weightedColimitOpposite_hom_ext {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}}
    {Y : SSet.{u}} {f g : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F).op ⟶ Y}
    (h : ∀ i, SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i) ≫ f =
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i) ≫ g) : f = g := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro z
  have he : (fun x ↦ f.app d (SSet.opObjEquiv.symm x)) =
      fun x ↦ g.app d (SSet.opObjEquiv.symm x) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitDegree_hom_ext W F d
    intro i x
    exact congrArg (fun t ↦ t.app d (SSet.opObjEquiv.symm x)) (h i)
  exact congrFun he (SSet.opObjEquiv z)

/-- 概要：coend の反転同型と余極限保存同型は標準 augmentation を結ぶ。
方針：各脚で重みの第一射影と余極限の脚を計算する。
規約：filtered 性や Kan 性は不要。使われ方：反転重みの augmentation の比較。 -/
lemma weightedColimitAugmentation_op_factor (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W (colimit.cocone F)) ≫
        (preservesColimitIso SSet.opFunctor F).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite.weightedColimitOppositeIso W F).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation (W ⋙ SSet.opFunctor) (colimit.cocone (F ⋙ SSet.opFunctor)) := by
  apply weightedColimitOpposite_hom_ext
  intro i
  calc
    _ = SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i ≫
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitAugmentation W (colimit.cocone F)) ≫
          (preservesColimitIso SSet.opFunctor F).hom := by
      rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = SSet.opFunctor.map (fst (F.obj i) (W.obj (Opposite.op i))) ≫
        SSet.opFunctor.map (colimit.ι F i) ≫ (preservesColimitIso SSet.opFunctor F).hom := by
      rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation, CategoryTheory.Functor.map_comp, Category.assoc]
      rfl
    _ = SSet.opFunctor.map (fst (F.obj i) (W.obj (Opposite.op i))) ≫
        colimit.ι (F ⋙ SSet.opFunctor) i := by rw [ι_preservesColimitIso_hom]
    _ = _ := by
      rw [reassoc_of% _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.WeightedColimitOpposite.weightedColimitOppositeIso_ι, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.weightedColimitι_augmentation]
      rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
