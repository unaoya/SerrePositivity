module

public import SerrePositivity.KST.Spectra.OrdinaryLoopUniversalNaturality
public import SerrePositivity.KST.Spectra.UniversalSourceParametricNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalCotensorConjugation

/-!
概要：通常円の同じ混合源の全族後合成を、元の二重 loop の curry 座標へ移す。
方針：同じ写像空間同型とその内部 Hom 像で共役し、元の標的区間の実辺を照合する。
規約：標準の反復 ihomAction との同定は別工程。使われ方：現在の交換区間の全族自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource
variable {P Z Z' : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom Z Z')

/-- 同じ全族後合成を、元の通常 loop 値の二重 loop 座標へ共役した実作用。 -/
def parametricLoopPost :
    LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) ⟶
      PointedObject.basedHom P (LoopExchangePaths.doubleLoop
        (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')) :=
  (mappingIso Z).inv ≫ PointedMapping.parametricPost source.{u} v ≫
    PointedObject.basedHomMap P (mappingIso Z').hom

/-- 同じ混合源の全族後合成は、共役した二重 loop 作用と同じ同型で厳密に可換。 -/
lemma mappingIso_parametricPost :
    (mappingIso Z).hom ≫ parametricLoopPost v =
      PointedMapping.parametricPost source.{u} v ≫
        PointedObject.basedHomMap P (mappingIso Z').hom := by
  simp only [parametricLoopPost, Iso.hom_inv_id_assoc]

/-- 指定した源作用の全族座標像を、元の同じ二重 loop の作用へ照合する。 -/
lemma mappingIso_parametric_conjugate_pre (a : source.{u} ⟶ source.{u})
    (t : LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z') ⟶
      LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))
    (ht : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z' ≫ (mappingIso Z').hom = (mappingIso Z').hom ≫ t) :
    (mappingIso Z).inv ≫
      ((PointedMapping.parametricPost source.{u} v ≫
        PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z')) ≫
          PointedObject.basedHomMap P (mappingIso Z').hom) =
      parametricLoopPost v ≫ PointedObject.basedHomMap P t := by
  have h : PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z') ≫
      PointedObject.basedHomMap P (mappingIso Z').hom =
    PointedObject.basedHomMap P (mappingIso Z').hom ≫ PointedObject.basedHomMap P t := by
    change (ihom P).map (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z') ≫ (ihom P).map (mappingIso Z').hom =
      (ihom P).map (mappingIso Z').hom ≫ (ihom P).map t
    rw [← CategoryTheory.Functor.map_comp, ht, CategoryTheory.Functor.map_comp]
  simpa only [parametricLoopPost, Category.assoc] using
    congrArg (fun m => (mappingIso Z).inv ≫ PointedMapping.parametricPost source.{u} v ≫ m) h

/-- 標的の元の交換区間の内部 Hom 像は、同じ内部 Hom 同型で共役した混合源区間。 -/
lemma loopExchangeInterval_parametricPath (P Z' : PointedSimplicialSet.{u})
    [KanComplex Z'.right] :
    ((loopExchangeInterval Z').basedIhomMap P).path =
      ((((sourceInterval Z').basedIhomMap P).basedPost
        (PointedMapping.cotensorIso P (mappingIso Z')).hom).pre
          (PointedMapping.cotensorIso P (mappingIso Z')).inv).path := by
  have h := PointedMapping.VerticalPath.basedIhomMap_path_congr (loopExchangeInterval Z')
    (((sourceInterval Z').basedPost (mappingIso Z').hom).pre (mappingIso Z').inv) P
    (loopExchangeInterval_path Z')
  exact h.trans ((sourceInterval Z').basedIhomMap_conjugate_path P (mappingIso Z'))

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
