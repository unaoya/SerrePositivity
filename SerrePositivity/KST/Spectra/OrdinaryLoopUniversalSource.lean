module

public import SerrePositivity.KST.Spectra.TwoLoopSourceCoordinates
public import SerrePositivity.KST.Spectra.OrdinaryLoopExchangeSign
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.UniversalSourceInterval

/-!
概要：通常円と外側二つの Kan 円の混合源に、一つの普遍交換区間を構成する。
方針：通常 loop の交換符号を元の源へ戻し、Kan 置換単位で実区間を一度選ぶ。
規約：標的別の成分から区間を選ばない。使われ方：元の通常円随伴への自然な移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource

/-- 内側を通常円、外側二つを Kan 円とする元の混合 smash。 -/
abbrev source : PointedSimplicialSet.{u} :=
  TwoLoopSource.source PointedSimplicialSet.circle.{u}

/-- 同じ混合源の外側二円の交換。 -/
abbrev swap : source.{u} ⟶ source.{u} := TwoLoopSource.swap PointedSimplicialSet.circle.{u}

/-- 同じ混合源の外側二円のうち内側の反転。 -/
abbrev reversal : source.{u} ⟶ source.{u} :=
  TwoLoopSource.reversal PointedSimplicialSet.circle.{u}

/-- 同じ混合源の写像空間の厳密な二重 loop 座標。 -/
abbrev mappingIso (Z : PointedSimplicialSet.{u}) :=
  TwoLoopSource.mappingIso PointedSimplicialSet.circle.{u} Z

/-- 同じ通常 loop を標的とする、外側二重 loop の後合成。 -/
abbrev loopPost {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z') :=
  TwoLoopSource.loopPost PointedSimplicialSet.circle.{u} v

/-- 通常円を含む元の源でも、交換・反転の前合成は全 Kan 標的で成分作用が一致する。 -/
lemma pre_swap_eq_reversal (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z).right =
      mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z).right := by
  have hinj : Function.Injective (mapπ₀ (mappingIso Z).hom.right) := by
    intro b c h
    have hi := congrArg Under.Hom.right (mappingIso Z).hom_inv_id
    change (mappingIso Z).hom.right ≫ (mappingIso Z).inv.right = 𝟙 _ at hi
    have hh := congrArg (mapπ₀ (mappingIso Z).inv.right) h
    simpa only [← mapπ₀_comp_apply, hi, mapπ₀_id_apply] using hh
  funext b
  apply hinj
  have hs := congrArg (fun k => mapπ₀ k.right b)
    (TwoLoopSource.mappingIso_pre_swap PointedSimplicialSet.circle.{u} Z)
  have hr := congrArg (fun k => mapπ₀ k.right b)
    (TwoLoopSource.mappingIso_pre_reversal PointedSimplicialSet.circle.{u} Z)
  simp only [Under.comp_right, mapπ₀_comp_apply] at hs hr
  exact hs.trans ((congrFun (ordinaryLoop_exchange_sign Z)
    (mapπ₀ (mappingIso Z).hom.right b)).trans hr.symm)

/-- 混合源の元の任意の族で、交換と反転の二辺は同じ成分を持つ。 -/
lemma component_swap_eq_reversal {Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : source.{u} ⟶ Z) :
    PointedMapping.componentOf (swap ≫ f) = PointedMapping.componentOf (reversal ≫ f) := by
  have h := congrFun (pre_swap_eq_reversal Z) (PointedMapping.componentOf f)
  simpa only [PointedMapping.componentOf, mapπ₀_mk, PointedMapping.familyVertex_pre] using h

/-- 元の混合源の実際の Kan 置換。 -/
abbrev universalTarget : PointedSimplicialSet.{u} := PointedKanReplacement.obj source.{u}

/-- 同じ混合源の実際の Kan 置換単位。 -/
def universalUnit : source.{u} ⟶ universalTarget.{u} := PointedKanReplacement.unit.app source

/-- 混合源の Kan 置換単位で一度選ぶ、元の二つの作用を結ぶ実区間。 -/
def universalPath : PointedMapping.VerticalPath (PointedObject.toPoint universalTarget.{u})
    (swap ≫ universalUnit) (reversal ≫ universalUnit) :=
  PointedMapping.basedPathOfComponent (component_swap_eq_reversal universalUnit)

/-- 全ての射・anodyne 性・実区間を供給した、通常円を内側にする普遍入力。 -/
def specification : UniversalSourceInterval.{u} where
  source := source
  target := universalTarget
  unit := universalUnit
  unit_anodyne := PointedKanReplacement.unit_anodyne source
  first := swap
  second := reversal
  path := universalPath

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
