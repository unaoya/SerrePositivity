module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeLegReverse
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.ExtOne

/-!
概要：二つの点の join から通常圏の nerve への全写像を、両端と混合辺で比較する。
方針：全一次単体を左右の境界と唯一の混合辺に分類する。
規約：比較する写像は全写像であり、π₀ の一致だけに置き換えない。
使われ方：元の分裂余錐の一点制限を元の定値余錐と厳密に照合する。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 二点の join から nerve への元の全写像は、両境界と唯一の混合辺で決まる。 -/
lemma pointJoinNerve_hom_ext {C : Type u} [Category.{u} C]
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0] ⟶ nerve C}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ g)
    (he : f.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))) = g.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex
        (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)))) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerve_hom_ext_one
  rintro ⟨l, a, b⟩
  fin_cases l
  · cases a
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr (Opposite.op ⦋1⦌)) b
  · have hz (a : (Δ[0] : SSet.{u}) _⦋0⦌) :
        a = stdSimplex.objEquiv.symm (𝟙 ⦋0⦌) := by
      apply SSet.stdSimplex.ext
      intro i
      apply Fin.ext
      have := (a i).isLt
      omega
    obtain rfl := hz a
    obtain rfl := hz b
    exact he
  · cases b
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hl (Opposite.op ⦋1⦌)) a

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
