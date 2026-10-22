module

public import SerrePositivity.InfinityCategories.F1.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.Core.RelativeCoslice

/-!
概要：底の図式を元のパラメータで動かした相対切断の族。
方針：内部 Hom の後合成を、元の底の図式の族に沿って引き戻す。
規約：対象の定義には充填性を要求せず、left fibration 性は元の射影から導く。
使われ方：under 圏上の切断による coherent 前層図式の strict 化。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の底の図式の族に厳密に重なる切断の族。 -/
def parametrizedSections {A E Y P : SSet.{u}} (p : E ⟶ Y) (a : P ⟶ (ihom A).obj Y) : SSet.{u} :=
  pullback ((ihom A).map p) a

/-- 切断の元の内部 Hom への包含。 -/
def parametrizedSectionsMap {A E Y P : SSet.{u}} (p : E ⟶ Y) (a : P ⟶ (ihom A).obj Y) :
    parametrizedSections p a ⟶ (ihom A).obj E := pullback.fst _ _

/-- 元のパラメータへの射影。 -/
def parametrizedSectionsProjection {A E Y P : SSet.{u}} (p : E ⟶ Y) (a : P ⟶ (ihom A).obj Y) :
    parametrizedSections p a ⟶ P := pullback.snd _ _

/-- 切断の族の底は元の図式の族に厳密に一致する。 -/
lemma parametrizedSections_condition {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) :
    parametrizedSectionsMap p a ≫ (ihom A).map p = parametrizedSectionsProjection p a ≫ a :=
  pullback.condition

instance parametrizedSectionsProjection_leftFibration {A E Y P : SSet.{u}} (p : E ⟶ Y)
    [LeftFibration p] (a : P ⟶ (ihom A).obj Y) :
    LeftFibration (parametrizedSectionsProjection p a) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := (ihom A).map p))⟩

/-- 同じ切断の族への写像は元の二成分で決まる。 -/
lemma parametrizedSections_hom_ext {A E Y P K : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) {f g : K ⟶ parametrizedSections p a}
    (hmap : f ≫ parametrizedSectionsMap p a = g ≫ parametrizedSectionsMap p a)
    (hbase : f ≫ parametrizedSectionsProjection p a =
      g ≫ parametrizedSectionsProjection p a) : f = g :=
  pullback.hom_ext hmap hbase

end SerrePositivity.InfinityCategories.F2.Ind
