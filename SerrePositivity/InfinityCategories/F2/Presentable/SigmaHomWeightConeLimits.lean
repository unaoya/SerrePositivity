module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaHomWeightComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaRestrictedLimits
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafUniverseArbitraryColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitMappingComparison
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp

/-!
概要：元の P_Σ sifted 余極限全余錐は、全 Hom 係数族の同じ極限錐を与える。
方針：包含と前層宇宙変更の保存を全 co-Yoneda へ送り、元の全係数で制限する。
規約：元の指定全余錐と全標的係数の自然性を保持する。
使われ方：左 Kan 延長の全 Hom 族の比較による sifted 余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：元の P_Σ sifted 余極限を、同じ大きい前層値包含が保存する。
方針：元の包含の保存と前層宇宙変更の任意形状での保存を合成する。
規約：元の余錐の宇宙持ち上げそのものの像を判定する。
使われ方：元の全 Hom 係数族に適用する大きい前層余極限。 -/
lemma sigmaUniverseInclusion_map_isColimit {I C : SSet.{u}} [IsSiftedInfinity I]
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SigmaPresheafInfinity C)
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (sigmaUniverseInclusion C)
      (JoinCocone.ulift.{u + 1, u + 2} c)) := by
  unfold sigmaUniverseInclusion
  rw [F2.Compact.mapJoinCocone_universe_comp]
  exact presheafUniverseDiagram_map_isColimit_arbitraryShape _ _
    (sigmaInclusion_map_isColimit p c hc)

/-- 概要：元の sifted 全余錐からの全自然変換空間族は、元の全係数で極限となる。
方針：同じ大きい前層余極限の反転に全 co-Yoneda を適用し、係数評価を制限する。
規約：全関手同型による比較前の元の自然変換空間族を用いる。
使われ方：元の左 Kan 延長の全 Hom 極限性への移送。 -/
lemma sigmaHomWeightFamily_map_isLimit {I C : SSet.{u}} [IsSiftedInfinity I]
    {E : SSet.{u + 1}} [Quasicategory E]
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E)
    (p : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ SigmaPresheafInfinity C)
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsLimitCone (mapJoinCone (sigmaHomWeightFamily F₀)
      (JoinCone.ulift.{u + 2, u + 3}
        (F1B.coconeReverseCone (JoinCocone.ulift.{u + 1, u + 2} c)))) := by
  let d := JoinCocone.ulift.{u + 1, u + 2} c
  have hU := (F2.isLimitCone_reverse_postcomp_iff d (sigmaUniverseInclusion C)).mpr
    (sigmaUniverseInclusion_map_isColimit p c hc)
  change IsLimitCone (mapJoinCone
    ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (sigmaUniverseInclusion C)) ≫
      (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
        (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
          (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}))
    (JoinCone.ulift.{u + 2, u + 3} (F1B.coconeReverseCone d)))
  rw [F2.Presentable.mapJoinCone_universe_comp]
  exact coyonedaInfinityMap_restricted_isLimit (presheafHomWeightDiagram F₀) _ hU

end SerrePositivity.InfinityCategories.HomotopyLimits
