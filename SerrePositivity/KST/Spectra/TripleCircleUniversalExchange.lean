module

public import SerrePositivity.KST.Spectra.TripleCircleCoordinates
public import SerrePositivity.KST.Spectra.KanLoopExchangeSign
public import SerrePositivity.KST.Spectra.PointedKanReplacement
public import SerrePositivity.KST.Spectra.PointedBasedPathCalculus

/-!
概要：三つの円の Kan 置換単位で交換符号を比較し、一つの普遍的な区間を選ぶ。
方針：三重 loop の符号定理を同じ curry 同型で元の源の二辺へ戻す。
規約：標的ごとに区間を選ばない。使われ方：全標的への anodyne 制限による区間移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.TripleCircle

/-- 三つの円の元の交換と反転は、任意の Kan 標的への前合成の成分作用が一致する。 -/
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
  have hs := congrArg (fun k => mapπ₀ k.right b) (mappingIso_pre_swap Z)
  have hr := congrArg (fun k => mapπ₀ k.right b) (mappingIso_pre_reversal Z)
  simp only [Under.comp_right, mapπ₀_comp_apply] at hs hr
  exact hs.trans ((congrFun (kanLoop_exchange_sign Z)
    (mapπ₀ (mappingIso Z).hom.right b)).trans hr.symm)

/-- 元の三重 smash の任意の族で、交換した二辺と反転した二辺の成分が一致する。 -/
lemma component_swap_eq_reversal {Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (f : source.{u} ⟶ Z) :
    PointedMapping.componentOf (swap ≫ f) = PointedMapping.componentOf (reversal ≫ f) := by
  have h := congrFun (pre_swap_eq_reversal Z) (PointedMapping.componentOf f)
  simpa only [PointedMapping.componentOf, mapπ₀_mk, PointedMapping.familyVertex_pre] using h

/-- 普遍的な三つの円の標的は、元の smash の Kan 置換。 -/
abbrev universalTarget : PointedSimplicialSet.{u} := PointedKanReplacement.obj source.{u}

/-- 同じ普遍的入力の Kan 置換単位。 -/
def universalUnit : source.{u} ⟶ universalTarget.{u} := PointedKanReplacement.unit.app source

/-- この同じ単位への制限は、全標的への族を移すための anodyne 射。 -/
lemma universalUnit_anodyne : SSet.anodyneExtensions universalUnit.{u}.right :=
  PointedKanReplacement.unit_anodyne source

/-- 三つの円の普遍的入力で一度だけ選ぶ、交換符号の同じ実区間。 -/
def universalExchangePath :
    PointedMapping.VerticalPath (PointedObject.toPoint universalTarget.{u})
      (swap ≫ universalUnit) (reversal ≫ universalUnit) :=
  PointedMapping.basedPathOfComponent (component_swap_eq_reversal universalUnit)

end SerrePositivity.KST.Spectra.TripleCircle
