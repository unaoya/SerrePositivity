module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterVertex
public import SerrePositivity.KST.Spectra.D3PointedKanEndpointZeros

/-!
概要：元の cofiber の制限射を、点つき Kan ∞ 圏の実極限錐へ移す。
方針：同じ点つき引き戻しの Hom 極限性と、元の端点包含による fibration を使う。
規約：新しい loop 関手を仮定せず、元の制限射・頂点・錐のまま認証する。
使われ方：実端点パラメータ全四角形族の引き戻し性の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance d3CofiberPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory
variable {A B : PointedSimplicialSet.{u}} (i : A ⟶ B) (Y : PointedKanObject.{u})

/-- 元の cofiber 正方形を同じ Kan Hom 対象の通常引き戻し錐にする。 -/
def d3PointedKanCofiberOrdinaryCone :
    PullbackCone
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj) :
        (d3PointedKanIhom B).obj Y ⟶ (d3PointedKanIhom A).obj Y)
      (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint A) Y.obj) :
        (d3PointedKanIhom PointedObject.point).obj Y ⟶ (d3PointedKanIhom A).obj Y) :=
  PullbackCone.mk
    (ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (pointedCofiberProjection i) Y.obj) :
      (d3PointedKanIhom (pointedCofiber i)).obj Y ⟶ (d3PointedKanIhom B).obj Y)
    (ObjectProperty.homMk
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.fromPoint (pointedCofiber i)) Y.obj)) (by
        apply ObjectProperty.hom_ext
        exact (pointedCofiberMapping_isPullback i Y.obj).w)

/-- 同じ元の点つき引き戻し性を、Kan 性だけを忘れた錐の極限性へ接続する。 -/
def d3PointedKanCofiberOrdinaryCone_forget_isLimit :
    IsLimit (pointedKanProperty.ι.mapCone (d3PointedKanCofiberOrdinaryCone i Y)) :=
  (isLimitMapConePullbackConeEquiv pointedKanProperty.ι
    (d3PointedKanCofiberOrdinaryCone i Y).condition).symm
      (pointedCofiberMapping_isPullback i Y.obj).isLimit

/-- 同じ実錐を Hom と同じ宇宙の cospan へ厳密に持ち上げる。 -/
def d3PointedKanCofiberCone :=
  (d3PointedKanCofiberOrdinaryCone i Y).whisker
    (AsSmall.down : AsSmall.{u} WalkingCospan ⥤ WalkingCospan)

/-- 同じ点つき錐の極限性は、元の Kan 豊穣 Hom でも極限性を与える。 -/
def d3PointedKanCofiberCone_hom_isLimit (Z : PointedKanObject.{u}) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (d3PointedKanCofiberCone i Y) Z) := by
  have hc : IsLimit (pointedKanProperty.ι.mapCone (d3PointedKanCofiberCone i Y)) :=
    (d3PointedKanCofiberOrdinaryCone_forget_isLimit i Y).whiskerEquivalence
      (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm
  change IsLimit (((SimplicialCategory.sHomFunctor PointedKanObject.{u}).obj
    (Opposite.op Z)).mapCone (d3PointedKanCofiberCone i Y))
  rw [d3PointedKanHomFunctor]
  have hm := isLimitOfPreserves (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj) hc
  exact IsLimit.ofIsoLimit hm (CategoryTheory.Functor.mapConeMapCone
    (H := pointedKanProperty.ι) (H' := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor Z.obj)
    (d3PointedKanCofiberCone i Y))

/-- 元の単射パラメータによる同じ制限錐は、実際の Kan ∞ 極限錐。 -/
lemma d3PointedKanCofiberCone_isLimit [Mono i.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (d3PointedKanCofiberCone i Y)) := by
  let f : (d3PointedKanIhom B).obj Y ⟶ (d3PointedKanIhom A).obj Y :=
    ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y.obj)
  let g : (d3PointedKanIhom PointedObject.point).obj Y ⟶ (d3PointedKanIhom A).obj Y :=
    ObjectProperty.homMk (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (PointedObject.toPoint A) Y.obj)
  have : Fibration f.hom.right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration i Y.obj
  have (Z : PointedKanObject.{u}) : Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (AsSmall.down ⋙ cospan f g) Z).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := by
    change Fibration (eHomWhiskerLeft SSet Z.obj f.hom)
    rw [PointedEnrichment.whiskerLeft_eq]
    exact PointedMapping.post_fibration Z.obj f.hom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (d3PointedKanCofiberCone i Y)
    (d3PointedKanCofiberCone_hom_isLimit i Y)

/-- 実端点図式に、元の端点包含の単射性を供給した ∞ 極限錐。 -/
lemma d3PointedKanEndpointCone_isLimit (Y : PointedKanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (d3PointedKanCofiberCone _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y)) :=
  d3PointedKanCofiberCone_isLimit _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
