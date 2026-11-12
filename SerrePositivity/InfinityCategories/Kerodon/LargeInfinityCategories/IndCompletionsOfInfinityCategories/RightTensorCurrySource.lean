module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightTensorCurryMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation

/-!
概要：全円柱の右 curry は、指定始点での全評価と厳密に可換する。
方針：内部 Hom の前合成を随伴の評価表示へ移し、同じ単体で計算する。
規約：全パラメーターと元の指定始点を保持する。
使われ方：三境界を固定した円柱比較を、始点評価下の余錐比較へ移す。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：区間の右 curry 後の始点評価は、元の円柱の始点制限そのもの。
方針：前合成を評価へ戻して全次数で計算。規約：全係数を保持。使われ方：相対比較。 -/
lemma rightTensorCurryMap_evaluate_zero (A X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightTensorCurryMap A (Δ[1] : SSet.{u}) X ≫
      (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      (pre (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u}))).app X := by
  rw [← curry_uncurry ((pre (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u}))).app X),
    uncurry_pre]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro a
  change s.app m (α ≫ 𝟙 m)
    (A.map (𝟙 m) a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) m.unop.len) =
      s.app m (α ≫ 𝟙 m) ((SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})).app m a)
  simp only [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
