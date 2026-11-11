module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SectionFamilyProductBase
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedPointRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan

/-!
概要：積上の切断の族の一点制限の底は、元のパラメータと元の頂点のグラフ。
方針：既存の curry の評価公式を元の積の二射影で計算する。
規約：底の図式は全次数での等式として照合する。
使われ方：under 圏の初頂点評価を、元の fibration の値への実際の比較に正規化する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の底の族を一点で評価すると、元の頂点のグラフになる。 -/
lemma sectionFamilyProductBase_evaluate {A D : SSet.{u}} (B : SSet.{u}) (a : A ⟶ D)
    (v : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v = lift (𝟙 B) (SSet.const (a.app _ v)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, lift_fst, lift_snd]
  · rw [Category.assoc, lift_snd, lift_snd, ← Category.assoc, lift_fst, SSet.const_comp]

/-- 同じ一点制限の評価の底は、元の一点の像のグラフ。 -/
lemma sectionFamilyProductBase_point {A D : SSet.{u}} (B : SSet.{u}) (a : A ⟶ D)
    (i : (Δ[0] : SSet.{u}) ⟶ A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B a ≫ (pre i).app (B ⊗ D)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso (B ⊗ D)).hom =
        lift (𝟙 B) (SSet.const (a.app _ (i.app _ (stdSimplex.obj₀Equiv.symm 0)))) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionFamilyProductBase B a ≫ (pre i).app (B ⊗ D)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre, sectionFamilyProductBase_evaluate]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
