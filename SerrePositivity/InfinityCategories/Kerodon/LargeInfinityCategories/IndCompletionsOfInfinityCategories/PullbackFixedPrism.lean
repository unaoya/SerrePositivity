module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedBoundedPrism

/-!
概要：比較先での値が固定された全円柱を、同じ pullback 図式内へ戻す。
方針：第二射影の元の図式を定値に保ち、厳密な可換式から pullback へ持ち上げる。
規約：元の始端を等号で回収する。使われ方：全空間比較の coslice 図式の一段への輸送。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {K X Y Z : SSet.{u}} (f : X ⟶ Y) (p : Z ⟶ Y)
  (a : K ⟶ pullback f p) (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
  (h : H ≫ f = (snd (Δ[1] : SSet.{u}) K ≫ a ≫ pullback.snd f p) ≫ p)

/-- 比較先での値が固定された元の円柱の、同じ第二射影を保つ pullback への持ち上げ。 -/
def pullbackFixedPrism : (Δ[1] : SSet.{u}) ⊗ K ⟶ pullback f p :=
  pullback.lift H (snd Δ[1] K ≫ a ≫ pullback.snd f p) h

@[reassoc]
lemma pullbackFixedPrism_fst : pullbackFixedPrism f p a H h ≫ pullback.fst f p = H :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma pullbackFixedPrism_snd : pullbackFixedPrism f p a H h ≫ pullback.snd f p =
    snd (Δ[1] : SSet.{u}) K ≫ a ≫ pullback.snd f p := pullback.lift_snd _ _ _

/-- 元の円柱の始端の厳密な一致は、同じ pullback 内でも厳密に保たれる。 -/
lemma pullbackFixedPrism_zero (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ H = a ≫ pullback.fst f p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ pullbackFixedPrism f p a H h = a := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackFixedPrism_fst, h₀]
  · rw [Category.assoc, pullbackFixedPrism_snd, ← Category.assoc, ← Category.assoc]
    change (𝟙 K ≫ a) ≫ pullback.snd f p = _
    rw [Category.id_comp]

/-- 持ち上げた円柱は、両端とも元の第二射影を厳密に保つ。 -/
lemma pullbackFixedPrism_endpoint_snd (t : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint t K ≫ pullbackFixedPrism f p a H h) ≫ pullback.snd f p =
      a ≫ pullback.snd f p := by
  rw [Category.assoc, pullbackFixedPrism_snd, ← Category.assoc, ← Category.assoc]
  change (𝟙 K ≫ a) ≫ pullback.snd f p = _
  rw [Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
