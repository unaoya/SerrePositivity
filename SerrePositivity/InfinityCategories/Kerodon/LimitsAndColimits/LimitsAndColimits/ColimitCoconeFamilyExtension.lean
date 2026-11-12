module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamilies
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# 指定された部分族を保つ native 普遍余錐の全関手族

## 概要
図式のパラメーターの部分単体集合で指定した普遍余錐の族を、全体へ厳密に延長する。

## 方針
普遍余錐射影の引き戻しの trivial Kan fibration に対して、単射の持ち上げを使う。

## 規約
指定した全余錐は頂点だけでなく全単体的写像として保持する。

## 使われ方
HTT 4.2.4.1、Kerodon 7.1（Tag 02H1）。計算済みの実現余錐を保つ全関手族の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 部分パラメーターで指定した同じ普遍余錐を保ち、全図式族の上へ厳密に延長する。 -/
theorem exists_colimitCoconeFamily_extension {A₀ A K X : SSet.{u}} [Quasicategory X]
    (d : A ⟶ (ihom K).obj X)
    (hd : ∀ a : A _⦋0⦌,
      HasColimit ((functorVertexEquiv K X).symm (d.app (Opposite.op ⦋0⦌) a)))
    (i : A₀ ⟶ A) [Mono i] (s : A₀ ⟶ colimitCocones K X)
    (hs : s ≫ colimitCoconeProjection K X = i ≫ d) :
    ∃ f : A ⟶ colimitCocones K X,
      f ≫ colimitCoconeProjection K X = d ∧ i ≫ f = s := by
  let p := colimitCoconeProjection K X
  let q := pullback.snd p d
  have : TrivialKanFibration q := colimitCoconeProjection_pullback_trivialKanFibration d hd
  let a := pullback.lift s i hs
  have : HasLiftingProperty i q := TrivialKanFibration.mem (p := q) i inferInstance
  let sq : CommSq a i q (𝟙 A) := ⟨by simp only [a, q, p, pullback.lift_snd, Category.comp_id]⟩
  refine ⟨sq.lift ≫ pullback.fst p d, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, sq.fac_right, Category.id_comp]
  · rw [← Category.assoc, sq.fac_left]
    exact pullback.lift_fst s i hs

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
