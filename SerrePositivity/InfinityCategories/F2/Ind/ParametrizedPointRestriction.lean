module

public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedPointSections
public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedSectionAnodyne

/-!
概要：一点への制限を、元のパラメータ付き切断の同じ評価の引き戻しへ実現する。
方針：同じ一点への制限と、既存の一点切断の同型を合成する。
規約：元の底の族は動かしたまま保持する。使われ方：under 圏の初頂点での評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の一点への制限と同じ一点切断の評価同型の合成。 -/
def parametrizedSectionsPointRestriction {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    parametrizedSections p a ⟶
      pullback p ((a ≫ (pre i).app Y) ≫ (pointFunctorEvaluationIso Y).hom) :=
  parametrizedSectionsPre p a (a ≫ (pre i).app Y) i rfl ≫
    (parametrizedSectionsPointIso p (a ≫ (pre i).app Y)).hom

/-- 元の値写像を評価する同じ射の合成を保持する。 -/
lemma parametrizedSectionsPointRestriction_map {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    parametrizedSectionsPointRestriction p a i ≫ pullback.fst p _ =
      parametrizedSectionsMap p a ≫ (pre i).app E ≫ (pointFunctorEvaluationIso E).hom := by
  rw [parametrizedSectionsPointRestriction, Category.assoc, parametrizedSectionsPointIso_map,
    ← Category.assoc, parametrizedSectionsPre_map, Category.assoc]

/-- 同じ一点への制限は元のパラメータを厳密に保つ。 -/
lemma parametrizedSectionsPointRestriction_projection {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (i : (Δ[0] : SSet.{u}) ⟶ A) :
    parametrizedSectionsPointRestriction p a i ≫ pullback.snd p _ =
      parametrizedSectionsProjection p a := by
  rw [parametrizedSectionsPointRestriction, Category.assoc,
    parametrizedSectionsPointIso_projection, parametrizedSectionsPre_projection]

/-- left anodyne な同じ一点への制限は、元の評価の引き戻しへ trivial Kan。 -/
lemma parametrizedSectionsPointRestriction_trivialKanFibration {A E Y P : SSet.{u}}
    (p : E ⟶ Y) [LeftFibration p] (a : P ⟶ (ihom A).obj Y)
    (i : (Δ[0] : SSet.{u}) ⟶ A) (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (parametrizedSectionsPointRestriction p a i) := by
  have hr := parametrizedSectionsPre_trivialKanFibration p a (a ≫ (pre i).app Y) i rfl hi
  exact ⟨trivialKanFibrations.comp_mem _ _ hr.mem (MorphismProperty.rlp_of_isIso _ _)⟩

end SerrePositivity.InfinityCategories.F2.Ind
