module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeInterchange
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeCriterion
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：点ごとの標準 U 余極限から関手圏における相対余極限を構成する。
方針：空の指定部分について相対余錐の順序交換を適用し、内部 Hom の後合成へ戻す。
規約：パラメータの quasicategory 性は要求しない。
使われ方：相対 Kan 条件を全パラメータの写像空間判定へ渡す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：点ごとの操作的な U 余極限条件は関手圏の操作的な相対余極限条件を与える。
方針：指定部分を空とし、相対内部 Hom の比較を通常の後合成へ同定する。
規約：U やパラメータに充填性を要求しない。
使われ方：局所余錐のパラメータ付きの普遍性。 -/
lemma kanRelativeCoconeLifting_functor_of_pointwise {A J D E : SSet.{u}}
    (U : D ⟶ E) (f : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting ((ihom A).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanCoconeFamilyTranspose f) := by
  let sj := Functor.PullbackObjObj.ofIsInitial internalHom (⊥ : A.Subcomplex).ι U
    Subcomplex.isInitialBot
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_relativeFunctor_of_first_vertices U ⊥ sj f
    (fun _ s _ ↦ hf (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s))

/-- 概要：点ごとの標準 U 余極限は関手圏の標準相対余極限を与える。
方針：標準条件を操作的な条件へ変え、順序交換した余錐で標準条件へ戻す。
規約：U は inner fibration。添字 J とパラメータ A は任意。
使われ方：関手圏に値を取る相対左 Kan 条件の局所判定。 -/
lemma kanIsRelativeColimitCone_functor_of_pointwise {A J D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (f : A ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join J (Δ[0] : SSet.{u}))).obj D)
    (hf : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt f a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone ((ihom A).map U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanCoconeFamilyTranspose f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_of_lifting
  exact kanRelativeCoconeLifting_functor_of_pointwise U f
    (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeLifting_of_isRelativeColimitCone U _ (hf a))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
