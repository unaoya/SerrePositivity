module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseInternalHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.OppositeKanHomotopy
public import SerrePositivity.InfinityCategories.F2.Compact.YonedaEvaluationClassification

/-!
概要：小さい前層を、持ち上げた同じ底上の一段大きい空間値前層へ送る。
方針：内部 Hom の標準宇宙同型、空間の指定宇宙変更、反転の宇宙同型を合成する。
規約：元の前層族の全写像を保持し、対象ごとの選択で関手を代用しない。
使われ方：P_Σ の左 Kan 延長の全自然 Hom 表示に必要な前層の宇宙変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の内部 Hom の標準宇宙比較は、同じ元の点での評価を厳密に保つ。 -/
lemma uliftInternalHomComparison_evaluation {A B : SSet.{u}} (a : A _⦋0⦌) :
    uliftInternalHomComparison.{u, v} A B ≫ evaluateFunctorAt (ULift.up a) =
      (SSet.uliftFunctor.{v, u}).map (evaluateFunctorAt (Y := B) a) := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ小さい前層族の値を、一段大きい空間として読む元の宇宙変更関手。 -/
def presheafUniverseDiagram (C : SSet.{u}) :
    (SSet.uliftFunctor.{u + 2, u + 1}).obj (PresheafInfinity C) ⟶
      PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C) :=
  uliftInternalHomComparison
      ((SSet.uliftFunctor.{u + 1, u}).obj C.op) SpaceInfinity.{u} ≫
    (ihom _).map F2.Compact.spaceUniverseDiagram ≫
      (pre ((SSet.uliftFunctor.{u + 2, u + 1}).map
        (uliftOppositeIso.{u, u + 1} C).inv)).app SpaceInfinity.{u + 1}

/-- 元の前層の宇宙変更と評価は、同じ点の空間の宇宙変更へ厳密に可換。 -/
lemma presheafUniverseDiagram_evaluation (C : SSet.{u}) (c : C _⦋0⦌) :
    presheafUniverseDiagram C ≫ presheafInfinityEvaluation (ULift.up c) =
      (SSet.uliftFunctor.{u + 2, u + 1}).map (presheafInfinityEvaluation c) ≫
        F2.Compact.spaceUniverseDiagram := by
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の宇宙変更は、底の同じ全射に沿う前層制限とも厳密に可換。 -/
lemma presheafUniverseDiagram_restriction {C D : SSet.{u}} (f : C ⟶ D) :
    (SSet.uliftFunctor.{u + 2, u + 1}).map (presheafInfinityRestriction f) ≫
        presheafUniverseDiagram C =
      presheafUniverseDiagram D ≫
        presheafInfinityRestriction ((SSet.uliftFunctor.{u + 1, u}).map f) := by
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
