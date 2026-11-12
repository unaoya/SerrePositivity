module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanFromHorn
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma excisionCoreCospanFirstEdge_code :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFirstEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn = horn₂₂.ι₀₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

lemma excisionCoreCospanSecondEdge_code :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanSecondEdge.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn = horn₂₂.ι₁₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

def excisionCoreCospanHornIso : (horn 2 2 : SSet.{u}) ≅
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} where
  hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn
  inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn
  hom_inv_id := by
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_first,
        excisionCoreCospanFirstEdge_code, Category.comp_id]
    · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_second,
        excisionCoreCospanSecondEdge_code, Category.comp_id]
  inv_hom_id := by
    let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn_mono.{u}
    apply (cancel_mono _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn).mp
    rw [Category.assoc]
    have h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanToHorn = 𝟙 _ := by
      apply horn₂₂.isPushout.hom_ext
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_first,
          excisionCoreCospanFirstEdge_code, Category.comp_id]
      · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionCoreCospanFromHorn_second,
          excisionCoreCospanSecondEdge_code, Category.comp_id]
    rw [h, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
