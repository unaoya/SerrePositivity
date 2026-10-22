module

public import SerrePositivity.EInfinity.FrameHom.NerveCoconePrism
public import SerrePositivity.EInfinity.FrameHom.FrameRoofFiberPinchedProjection
public import SerrePositivity.InfinityCategories.Derived.SliceEvaluationPinched

/-!
# 通常の Over 図式の実 slice 評価は元の右脚の円柱

概要：同じ qY slice への Over 図式を評価すると、元の余錐の自然変換の像を得る。
方針：点図式の等式輸送を消し、uncurry の自然性と全 nerve prism の一致を接続する。
規約：同じ q・元の全円柱を保持し、quasicategory 性は仮定しない。
使われ方：実 corner の幾何的右脚を元の標準右脚へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory Limits Opposite SSet MonoidalCategory
open SerrePositivity.InfinityCategories FrameArrows
open scoped Simplicial

lemma sliceOverUncurry_pointTransport {S X : SSet.{u}} {p p' : (Δ[0] : SSet.{u}) ⟶ X}
    (h : p = p') (f : S ⟶ sliceOver p) :
    sliceOverUncurry (f ≫ (eqToIso (congrArg sliceOver h)).hom) = sliceOverUncurry f := by
  subst p'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

variable {I C : Type u} [Category.{u} I] [Category.{u} C] (Y : C) (T : I ⥤ Over Y)
  {E : SSet.{u}} (q : nerve C ⟶ E)

def nerveOverRightSliceMap : nerve I ⟶
    sliceOver (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (nerveVertex Y))) :=
  nerveMap T ≫ (F1B.kanNerveOverIso Y).hom ≫
    sliceOverPostcomp (SSet.yonedaEquiv.symm (nerveVertex Y)) q ≫
      (roofTargetSlicePointIso Y q).hom

lemma nerveOverRightSliceMap_uncurry : sliceOverUncurry (nerveOverRightSliceMap Y T q) =
    (F1B.kanNerveCoconeEquiv ((F1B.kanOverForgetCocone Y).whisker T)).val ≫ q := by
  have hpost := sliceOverUncurry_postcomp
    (nerveMap T ≫ (F1B.kanNerveOverIso Y).hom) q
  have hpre := sliceOverUncurry_precomp (F1B.kanNerveOverIso Y).hom (nerveMap T)
  rw [F1B.kanNerveOverIso_uncurry, F1B.kanNerveCocone_whisker] at hpre
  simp only [nerveOverRightSliceMap, roofTargetSlicePointIso, ← Category.assoc]
  rw [sliceOverUncurry_pointTransport (roofTargetPoint q (nerveVertex Y))]
  exact hpost.trans (congrArg (fun g => g ≫ q) hpre)

lemma nerveOverRightSliceMap_evaluation_h :
    (functorHomotopyPrecomp (roofSliceEvaluationHomotopy
      (q.app (op ⦋0⦌) (nerveVertex Y))) (nerveOverRightSliceMap Y T q)).h =
    (F1B.kanNerveNatTransHomotopy ((F1B.kanOverForgetCocone Y).whisker T).ι).h ≫ q := by
  rw [roofSliceEvaluationHomotopy_precomp_h, nerveOverRightSliceMap_uncurry]
  simpa only [Category.assoc] using congrArg (fun g => g ≫ q)
    (nerveCoconePrism_eq_natTrans (T ⋙ Over.forget Y)
      ((F1B.kanOverForgetCocone Y).whisker T))

end SerrePositivity.EInfinity.FrameHom
