module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndExtensionHomWeightComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaRestrictedLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafUniverseArbitraryColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitMappingComparison
public import SerrePositivity.InfinityCategories.F1B.CatInfinity.CoconeReversePostcomp

/-!
概要：全前層から元の全 Hom 係数前層への自然変換空間族。
方針：前層宇宙変更の後の全 co-Yoneda を同じ係数族で制限する。
規約：P_Σ や Ind へ制限する前の全族を構成する。
使われ方：密度表示と simplicial Ind 表示の Hom 極限の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：全前層を始域とする、元の Hom 係数への全自然変換空間族。
方針：同じ大きい前層への宇宙変更を全共同 Hom へ合成する。
規約：全標的係数で自然な関手族である。
使われ方：二つの全前層余極限表示に同じ Hom を適用する。 -/
def fullPresheafHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj (PresheafInfinity C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (presheafUniverseDiagram C)) ≫
    coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}

/-- 概要：全前層 Hom 族の Ind 制限は構成済みの同じ Ind 係数族。
方針：元の包含と宇宙変更の合成を展開する。
規約：同じ全写像の厳密な等式である。
使われ方：bar の全図式に沿う全 Hom 比較。 -/
lemma fullPresheafHomWeightFamily_indRestriction (κ : Cardinal.{u})
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (indInclusionPresheaf κ C))) ≫
      fullPresheafHomWeightFamily F₀ = indHomWeightFamily κ F₀ := by
  simp only [fullPresheafHomWeightFamily, indHomWeightFamily, indUniverseHomInclusion,
    Functor.map_comp, Category.assoc]

/-- 概要：全前層 Hom 族の元の Yoneda 制限は、元の大きい Yoneda 係数族と同型。
方針：同じ指定 Yoneda 宇宙比較を全共同 Hom へ送る。
規約：元の全係数を保持する。
使われ方：elements 密度図式への制限の比較。 -/
def fullPresheafHomWeightFamily_yonedaRestrictionIso
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    FunctorIso ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C))) ≫
      fullPresheafHomWeightFamily F₀) (yonedaHomWeightFamily F₀) := by
  have e := (FunctorIso.ulift.{u + 2, u + 3} (yonedaInfinityMap_universeIso C).op).postcomp
    (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2})
  simpa only [Functor.map_comp, Category.assoc, fullPresheafHomWeightFamily,
    yonedaHomWeightFamily] using e

omit [Quasicategory C] in
/-- 概要：元の全前層の小余極限は、同じ全 Hom 係数族で極限になる。
方針：前層宇宙変更の保存後に全 co-Yoneda と同じ係数制限を適用する。
規約：指定された同じ全余錐を保持し、sifted 性を要求しない。
使われ方：密度表示と bar 表示の共通の Hom 極限。 -/
lemma fullPresheafHomWeightFamily_map_isLimit {I : SSet.{u}}
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity C)
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsLimitCone (mapJoinCone (fullPresheafHomWeightFamily F₀)
      (JoinCone.ulift.{u + 2, u + 3}
        (F1B.coconeReverseCone (JoinCocone.ulift.{u + 1, u + 2} c)))) := by
  let d := JoinCocone.ulift.{u + 1, u + 2} c
  have hU := (F2.isLimitCone_reverse_postcomp_iff d (presheafUniverseDiagram C)).mpr
    (presheafUniverseDiagram_map_isColimit_arbitraryShape p c hc)
  change IsLimitCone (mapJoinCone
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (presheafUniverseDiagram C)) ≫
      (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
        (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
          (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}))
    (JoinCone.ulift.{u + 2, u + 3} (F1B.coconeReverseCone d)))
  rw [mapJoinCone_universe_comp]
  exact coyonedaInfinityMap_restricted_isLimit (presheafHomWeightDiagram F₀) _ hU

end SerrePositivity.InfinityCategories.F2.Presentable
