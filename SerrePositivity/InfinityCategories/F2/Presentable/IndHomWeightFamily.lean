module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndUniverseHomInclusion
public import SerrePositivity.InfinityCategories.F2.Presentable.YonedaWeightFamilyComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomCanonicalRightKan

/-!
概要：Ind 対象から元の Hom 係数前層への全自然変換空間族。
方針：大きい包含の全 co-Yoneda を同じ全係数関手で制限する。
規約：両変数の全自然性と元の Yoneda の右 Kan 条件を保持する。
使われ方：filtered 延長の全 Hom 族の表示。
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

/-- 概要：Ind の元の全前層から全 Hom 係数への自然変換空間を束ねる。
方針：同じ大きい前層圏の co-Yoneda と係数制限を合成する。
規約：各対象対の同値の族に弱めない。
使われ方：幾何学的実現の全標的係数での検査。 -/
def indHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj (IndInfinity κ C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (indUniverseHomInclusion κ C)) ≫
    coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}

/-- 概要：同じ Ind 自然変換空間族は持ち上げた元の Yoneda の右 Kan 延長。
方針：大きい包含の全標準余極限条件を全 Hom 族へ移す。
規約：同じ全族と恒等単位を保持する。
使われ方：二つの全 Hom 表示の一意性による比較。 -/
lemma indHomWeightFamily_isRightKanExtension
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    IsRightKanExtension
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))))
      ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫ indHomWeightFamily κ F₀)
      (indHomWeightFamily κ F₀)
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫ indHomWeightFamily κ F₀)) :=
  homCanonical_isRightKanExtension _ (indUniverseHomInclusion κ C)
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀))
    (indUniverseHomInclusion_canonicalColimits κ)

/-- 概要：同じ Ind Hom 係数族の Yoneda 制限は元の大きい Yoneda の全族と同型。
方針：包含の Yoneda 宇宙比較を全 co-Yoneda と係数制限へ送る。
規約：全 C と全標的係数で自然な同型。
使われ方：延長の回収同型との合成。 -/
def indHomWeightFamily_restrictionIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (indYoneda κ C))) ≫ indHomWeightFamily κ F₀)
      (yonedaHomWeightFamily F₀) := by
  have e := (FunctorIso.ulift.{u + 2, u + 3} (indUniverseHomYonedaIso κ C).op).postcomp
    (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2})
  simpa only [Functor.map_comp, Category.assoc, indHomWeightFamily, yonedaHomWeightFamily] using e

end SerrePositivity.InfinityCategories.F2.Presentable
