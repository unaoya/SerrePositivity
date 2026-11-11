module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentReverseSlicePost
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionPrismPost
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionReverse

/-!
概要：元の反転合成 prism 全体は、同じ指定終域射の後合成に厳密に自然。
方針：元の右 slice prism の自然性を、同じ反転と係数交換で移す。
規約：元の時刻・二つの全 Hom を保持。使われ方：元の指定輸送比較への適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z W : C}

/-- 元の二 Hom の係数交換は、同じ第二射の後合成と厳密に可換。 -/
lemma coherentReverseCompositionParameters_post (g : Z ⟶ W) :
    coherentReverseCompositionParameters X Y Z ≫
      SSet.opFunctor.map (𝟙 ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)) ⊗ₘ
        (SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g)) =
      (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g)) ⊗ₘ
        𝟙 (((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op)) ≫
          coherentReverseCompositionParameters X Y W := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 元の反転合成 prism の指定後合成は、同じ動く第二 Hom を後合成した制限そのもの。 -/
lemma coherentCompositionReversePrism_post (g : Z ⟶ W) :
    coherentCompositionReversePrism X Y Z ≫ coherentReverseSlicePost g =
      (Δ[1] ◁ (SSet.opFunctor.map
        ((SSet.uliftFunctor.{v, u}).map (eHomWhiskerLeft SSet Y g)) ⊗ₘ
          𝟙 (((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y)).op))) ≫
            coherentCompositionReversePrism X Y W := by
  dsimp only [coherentCompositionReversePrism]
  rw [Category.assoc, reversePointSlicePrism_coherent_post,
    coherentCompositionPrism_post, reversePointSlicePrism_precomp,
    ← Category.assoc, ← whiskerLeft_comp, coherentReverseCompositionParameters_post,
    whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
