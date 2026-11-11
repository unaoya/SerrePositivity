module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedPointSections
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedSectionAnodyne

/-!
概要：一点への制限を、元のパラメータ付き切断の同じ評価の引き戻しへ実現する。
方針：同じ一点への制限と、既存の一点切断の同型を合成する。
規約：元の底の族は動かしたまま保持する。使われ方：under 圏の初頂点での評価。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の一点への制限と同じ一点切断の評価同型の合成。 -/
def parametrizedSectionsPointRestriction {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p a ⟶
      pullback p ((a ≫ (pre i).app Y) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso Y).hom) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre p a (a ≫ (pre i).app Y) i rfl ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPointIso p (a ≫ (pre i).app Y)).hom

/-- 元の値写像を評価する同じ射の合成を保持する。 -/
lemma parametrizedSectionsPointRestriction_map {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    parametrizedSectionsPointRestriction p a i ≫ pullback.fst p _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a ≫ (pre i).app E ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.pointFunctorEvaluationIso E).hom := by
  rw [parametrizedSectionsPointRestriction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPointIso_map,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_map, Category.assoc]

/-- 同じ一点への制限は元のパラメータを厳密に保つ。 -/
lemma parametrizedSectionsPointRestriction_projection {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    parametrizedSectionsPointRestriction p a i ≫ pullback.snd p _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a := by
  rw [parametrizedSectionsPointRestriction, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPointIso_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_projection]

/-- left anodyne な同じ一点への制限は、元の評価の引き戻しへ trivial Kan。 -/
lemma parametrizedSectionsPointRestriction_trivialKanFibration {A E Y P : SSet.{u}}
    (p : E ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : P ⟶ (ihom A).obj Y)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (parametrizedSectionsPointRestriction p a i) := by
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsPre_trivialKanFibration p a (a ≫ (pre i).app Y) i rfl hi
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ hr.mem (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
