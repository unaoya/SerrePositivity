module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.Definition
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.UniverseTensorEndpoints

/-!
概要：元の指定右 Kan 余単位を、同じ図式の宇宙持ち上げの間の全ホモトピーとして使う。
方針：既存の全円柱の移送で写し、始端だけを元の関手の合成則で正規化する。
使われ方：Kerodon §7.3（Tag 02Y1）、HTT 6.2.2.6 の任意の係数での降下。
規約：元のホモトピーの全族を保持し、別の変換を選ばない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 元の余単位の全円柱を同じ宇宙移送で写した指定代表。 -/
def kanRightCounitUlift {K C D : SSet.{u}} {δ : K ⟶ C} {F₀ : K ⟶ D} {F : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) :
    SSet.Homotopy ((SSet.uliftFunctor.{v, u}).map δ ≫ (SSet.uliftFunctor.{v, u}).map F)
      ((SSet.uliftFunctor.{v, u}).map F₀) where
  h := simplexTensorMap.{v} α.h
  h₀ := by
    rw [simplexTensorMap_zero, α.h₀, Functor.map_comp]
    rfl
  h₁ := by
    rw [simplexTensorMap_one, α.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
