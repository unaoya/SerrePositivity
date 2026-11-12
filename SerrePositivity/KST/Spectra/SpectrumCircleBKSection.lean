module

public import SerrePositivity.KST.Spectra.SpectrumCircleBKEndPoint

/-!
概要：元の cotensor 恒等射の像から、全 BK 重み上の元のスペクトル Hom の切断を作る。
方針：end の点を uncurry し、単位パラメーターを自然に除く。
規約：中央成分は元の普遍評価に厳密一致。使われ方：切断点の Hom 前合成族の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleSectionSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 元の恒等射の比較像を、全 BK 重み上の実際の自然変換として読む。 -/
def circleBKSection (Y : OmegaSpectrum.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) (cotensor PointedSimplicialSet.circle Y) :=
  (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry (circleBKEndPointMap Y)

/-- 切断の中央は、元の普遍評価を指定した円パラメーターで読む射そのもの。 -/
lemma circleBKSection_central (Y : OmegaSpectrum.{u}) :
    (circleBKSection Y).app (AsSmall.up.obj .one) =
      circleBKParameter.{u} ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right := by
  change (ρ_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan)).obj
      (AsSmall.up.obj .one))).inv ≫ uncurry (circleBKEndPointMap Y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) (cotensor PointedSimplicialSet.circle Y))
          (AsSmall.up.obj .one)) = _
  rw [circleBKEndPointMap_central]
  simp only [MonoidalClosed.curry', uncurry_curry, Iso.inv_hom_id_assoc]

/-- 固定 Hom cospan の両端が終対象なので、元の BK end への射は中央で決まる。 -/
lemma pointLoopHomEnd_hom_ext (X Y : OmegaSpectrum.{u}) {P : SSet.{u}}
    {a b : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X)}
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one) =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (pointLoopDiagram Y) X) (AsSmall.up.obj .one)) : a = b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  rintro ⟨i⟩
  cases i with
  | none => exact h
  | some i =>
    cases i <;> apply uncurry_injective <;> exact (mappingPoint_isTerminal X).hom_ext _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum
