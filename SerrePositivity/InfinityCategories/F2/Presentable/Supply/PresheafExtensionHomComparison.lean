module

public import SerrePositivity.InfinityCategories.F2.Presentable.FullPresheafHomWeightFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafYonedaLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.YonedaWeightLeftKan

/-!
概要：全前層の係数 Hom 族と、指定された Yoneda 左 Kan 延長の全 Hom 族を比較する。
方針：両族を同じ持ち上げた Yoneda の右 Kan 延長として制限の同型から比較する。
規約：元の指定単位を保持し、始域・終域の両変数で全自然な同型を構成する。
使われ方：P-12 の Yoneda 模型を元の関手圏の Hom へ戻すための普遍性入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {A : SSet.{u}} [Quasicategory A]
    {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：前層の元の宇宙変更の全標準 Yoneda 余錐は余極限。
方針：既存の同じ恒等単位付き左 Kan 条件から標準余錐を回収する。
規約：元の宇宙変更を使う。使われ方：全前層 Hom 族の右 Kan 条件。 -/
lemma presheafUniverse_canonicalColimits
    (a : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (PresheafInfinity A)) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap A))
      (presheafUniverseDiagram A) a) := by
  apply F1B.kanLeftKanExtension_canonicalColimits_of_unit_isIso _ _
    (presheafUniverseDiagram_isLeftKanExtension A)
  simp only [functorHomotopyRefl_hom]
  exact ⟨⟨𝟙 _, Category.id_comp _, Category.comp_id _⟩⟩

/-- 概要：全前層の係数 Hom 族は元の持ち上げた Yoneda の右 Kan 延長。
方針：宇宙変更の標準余錐を全共同 Hom と同じ係数制限へ送る。
規約：全前層と全標的係数を扱う。使われ方：右 Kan の一意性による全自然比較。 -/
lemma fullPresheafHomWeightFamily_isRightKanExtension
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D) :
    IsRightKanExtension
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap A))))
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap A))) ≫
        fullPresheafHomWeightFamily F₀)
      (fullPresheafHomWeightFamily F₀)
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap A))) ≫
        fullPresheafHomWeightFamily F₀)) :=
  homCanonical_isRightKanExtension _ (presheafUniverseDiagram A)
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀))
    presheafUniverse_canonicalColimits

variable {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D}
    {L : PresheafInfinity A ⟶ D}
    (β : SSet.Homotopy F₀ (yonedaInfinityMap A ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap A) F₀ L β)

/-- 概要：指定左 Kan 延長の全 Hom 族の Yoneda 制限は元の図式の Hom 族と同型。
方針：指定単位の可逆性による回収を持ち上げ、全 co-Yoneda へ写す。
規約：元の指定単位を使う。使われ方：二つの右 Kan 延長の制限比較。 -/
def presheafExtensionHom_restrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap A))) ≫
      canonicalLiftedHomFamily L) (liftedHomWeightFamily F₀) := by
  have := presheafYonedaLeftKan_unit_isIso β hβ
  let r : FunctorIso (yonedaInfinityMap A ≫ L) F₀ :=
    (asIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))).symm
  have e := (FunctorIso.ulift.{u + 2, u + 3}
    (FunctorIso.ulift.{u + 1, u + 2} r).op).postcomp
      (coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
  simpa only [Functor.map_comp, Category.assoc, canonicalLiftedHomFamily,
    liftedHomWeightFamily] using e

/-- 概要：全前層係数族と指定左 Kan 延長の全 Hom 族は両変数で全自然同型。
方針：元の Yoneda 評価と指定単位で制限を比較し、右 Kan 一意性を適用する。
規約：対象ごとの写像空間同値の存在へ弱めない。
使われ方：全図式に沿う Hom 族の普遍性の移送。 -/
def presheafExtensionHom_liftedIso :
    FunctorIso (fullPresheafHomWeightFamily F₀) (canonicalLiftedHomFamily L) :=
  rightKanReflRestrictionIso _ (fullPresheafHomWeightFamily_isRightKanExtension F₀)
    (canonicalLiftedHomFamily_isRightKanExtension (yonedaInfinityMap A) L
      (presheafYonedaLeftKan_canonicalColimits β hβ))
    (fullPresheafHomWeightFamily_yonedaRestrictionIso F₀ ≪≫
      yonedaHomWeightFamily_evaluationIso F₀ ≪≫ homWeightEvaluationFamily_liftedIso F₀ ≪≫
        (presheafExtensionHom_restrictionIso β hβ).symm)

end SerrePositivity.InfinityCategories.F2.Presentable
