module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation

/-!
概要：頂点を持つパラメータの定値関手への Hom 写像は単射。
方針：定値関手の射を一つの頂点で評価すると元の射を回収できることを使う。
規約：パラメータの非空性は実際の頂点として受け取る。
使われ方：B1 の定値 Hom の単位比較から各点の一意性を取り出す。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：定値関手への射をパラメータの頂点で評価すると元の射。
方針：単体ごとの定値単体への評価を計算する。
規約：quasicategory 性は不要。使われ方：Hom の単射性の評価による検出。 -/
lemma constantFunctorMap_evaluate {A X : SSet.{u}} (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a = 𝟙 X := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  change X.map (𝟙 d) x = x
  exact CategoryTheory.Functor.map_id_apply X d x

/-- 概要：パラメータに頂点があれば定値関手への Hom 写像は単射。
方針：両端の輸送を消去し、評価による関手の左逆を使う。
規約：X と A の quasicategory 性は不要。
使われ方：各点の単位 Hom 比較の単射性の回収。 -/
lemma constantFunctorHomMap_injective {A X : SSet.{u}} (a : A _⦋0⦌)
    (x y : X _⦋0⦌) : Function.Injective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap A (x := x) (y := y)) := by
  intro α β h
  let C := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X)).toFunctor
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor
  have hCE : C ⋙ E = 𝟭 (hoFunctor.obj X) := by
    change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap A X) ≫
      hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).toFunctor = _
    rw [← Functor.map_comp, constantFunctorMap_evaluate, CategoryTheory.Functor.map_id]
    rfl
  have hm : C.map α = C.map β := by
    have hh := congrArg (fun k : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom A X x y ↦
      eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A x)) ≫ k ≫
        eqToHom (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex A y)).symm) h
    simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap, Category.assoc, C] using hh
  have hh := congrArg E.map hm
  change (C ⋙ E).map α = (C ⋙ E).map β at hh
  rw [hCE] at hh
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
