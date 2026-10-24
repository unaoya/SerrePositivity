module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndHomWeightFamily
public import SerrePositivity.InfinityCategories.F2.Presentable.CanonicalLiftedHomFamily
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCanonical
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaLiftedHomRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.RightKanRestrictionIso

/-!
概要：Ind 延長の全 Hom 族と元の前層係数族の全自然比較。
方針：同じ Yoneda 単位で制限を比較し、両右 Kan 条件の一意性を使う。
規約：Ind 側を編集せず、元の全関手と指定単位を保持する。
使われ方：filtered 延長と bar 実現による g4 の標的仮定の縮小。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)

/-- 概要：持ち上げた Ind 延長の全 Hom 制限は元の図式の全 Hom 族と同型。
方針：元の指定単位による回収同型を全 co-Yoneda へ送る。
規約：同じ全係数を保持する。
使われ方：二つの Hom 族の制限の比較。 -/
def indExtensionHomWeight_restrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫
      canonicalLiftedHomFamily G) (liftedHomWeightFamily F₀) := by
  have e := (FunctorIso.ulift.{u + 2, u + 3}
    (FunctorIso.ulift.{u + 1, u + 2} (indLeftKanExtensionRecoveryIso κ β hβ)).op).postcomp
      (coyonedaInfinityMap ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
  simpa only [Functor.map_comp, Category.assoc, canonicalLiftedHomFamily,
    liftedHomWeightFamily] using e

/-- 概要：元の自然変換空間族と Ind 延長の Hom 族の制限は全自然同型。
方針：元の Yoneda 評価同型と指定単位の回収を合成する。
規約：同じ二変数の全族を比較する。
使われ方：右 Kan 一意性による元の全族への延長。 -/
def indExtensionHomWeight_liftedRestrictionIso :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫ indHomWeightFamily κ F₀)
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫
          canonicalLiftedHomFamily G) :=
  indHomWeightFamily_restrictionIso κ F₀ ≪≫ yonedaHomWeightFamily_evaluationIso F₀ ≪≫
    homWeightEvaluationFamily_liftedIso F₀ ≪≫ (indExtensionHomWeight_restrictionIso κ β hβ).symm

/-- 概要：Ind 延長の全 Hom 族は元の全前層係数族と両変数で自然同型。
方針：同じ元の Yoneda に沿う二つの右 Kan 条件を比較する。
規約：各対象対の写像空間同値の存在だけへ弱めない。
使われ方：幾何学的実現と Hom の極限の自然な移送。 -/
def indExtensionHomWeight_liftedIso :
    FunctorIso (indHomWeightFamily κ F₀) (canonicalLiftedHomFamily G) :=
  rightKanReflRestrictionIso _ (indHomWeightFamily_isRightKanExtension κ F₀)
    (canonicalLiftedHomFamily_isRightKanExtension (indYoneda κ C) G
      (indLeftKanExtension_canonicalColimits κ β hβ))
    (indExtensionHomWeight_liftedRestrictionIso κ β hβ)

end SerrePositivity.InfinityCategories.F2.Presentable
