module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：小余積と幾何学的実現の存在条件を、元の全図式で定義する。
方針：小さい離散 nerve と単体次数の反対圏の nerve を明示する。
規約：添字の宇宙は u、標的は u+1。instance の追加条件にしない。
使われ方：二種類の余極限からの全小余極限の構成。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
universe u
open CategoryTheory SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

/-- 概要：任意の小さい離散全図式の余極限が存在する条件。
方針：各離散 nerve の持ち上げからの全関手を量化する。
規約：空添字も含み、頂点の集合だけへ弱めない。
使われ方：bar 図式の各次数の左 Kan 延長。 -/
def HasSmallCoproducts (X : SSet.{u + 1}) : Prop :=
  ∀ (I : Type u) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete I)) ⟶ X),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F

/-- 概要：任意の小さい単体的全図式の幾何学的実現が存在する条件。
方針：宇宙を合わせた反対単体圏の nerve からの全関手を量化する。
規約：全ての面と退化を持つ図式を扱う。
使われ方：bar の各次数を合わせた全余極限の構成。 -/
def HasSmallGeometricRealizations (X : SSet.{u + 1}) : Prop :=
  ∀ F : (SSet.uliftFunctor.{u + 1, u}).obj
    (nerve (ULiftHom.{u} (ULift.{u} SimplexCategoryᵒᵖ))) ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F

/-- 概要：全小余極限の存在は小余積の存在を含む。
方針：元の全図式条件を離散形状に適用する。
規約：同じ宇宙を保持する。
使われ方：一般補題の必要条件。 -/
lemma HasSmallColimits.hasSmallCoproducts {X : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) : HasSmallCoproducts X := fun I F ↦ hX (nerve (Discrete I)) F

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallColimits (hasSmallCoproducts)


/-- 概要：全小余極限の存在は小さい幾何学的実現の存在を含む。
方針：元の全図式条件を反対単体次数の形状に適用する。
規約：元の全単体的図式を保持する。
使われ方：一般補題の必要条件。 -/
lemma HasSmallColimits.hasSmallGeometricRealizations {X : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) : HasSmallGeometricRealizations X := fun F ↦ hX _ F

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallColimits (hasSmallGeometricRealizations)


end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
