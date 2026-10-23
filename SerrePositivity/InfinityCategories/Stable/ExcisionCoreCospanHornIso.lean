module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCospanFromHorn
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.SliceRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Core.LeftPrism
public import SerrePositivity.InfinityCategories.Core.PrismFilling
public import SerrePositivity.InfinityCategories.Stable.PosetClosureRetraction

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
namespace SerrePositivity.InfinityCategories

lemma excisionCoreCospanFirstEdge_code :
    excisionCoreCospanFirstEdge.{u} ≫ excisionCoreCospanToHorn = horn₂₂.ι₀₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  rw [Category.assoc, excisionCoreCospanToHorn_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

lemma excisionCoreCospanSecondEdge_code :
    excisionCoreCospanSecondEdge.{u} ≫ excisionCoreCospanToHorn = horn₂₂.ι₁₂ := by
  apply (cancel_mono (horn 2 2).ι).mp
  rw [Category.assoc, excisionCoreCospanToHorn_ι]
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  fin_cases i <;> decide

def excisionCoreCospanHornIso : (horn 2 2 : SSet.{u}) ≅
    nerve ExcisionCoreCospanIndex.{u} where
  hom := excisionCoreCospanFromHorn
  inv := excisionCoreCospanToHorn
  hom_inv_id := by
    apply horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, excisionCoreCospanFromHorn_first,
        excisionCoreCospanFirstEdge_code, Category.comp_id]
    · rw [← Category.assoc, excisionCoreCospanFromHorn_second,
        excisionCoreCospanSecondEdge_code, Category.comp_id]
  inv_hom_id := by
    let := excisionCoreCospanToHorn_mono.{u}
    apply (cancel_mono excisionCoreCospanToHorn).mp
    rw [Category.assoc]
    have h : excisionCoreCospanFromHorn.{u} ≫ excisionCoreCospanToHorn = 𝟙 _ := by
      apply horn₂₂.isPushout.hom_ext
      · rw [← Category.assoc, excisionCoreCospanFromHorn_first,
          excisionCoreCospanFirstEdge_code, Category.comp_id]
      · rw [← Category.assoc, excisionCoreCospanFromHorn_second,
          excisionCoreCospanSecondEdge_code, Category.comp_id]
    rw [h, Category.comp_id, Category.id_comp]

end SerrePositivity.InfinityCategories
