module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaElementsLeftKanModel
public import SerrePositivity.InfinityCategories.F2.Ind.PullbackRightBaseIso
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftKanShapeCommaProjection

/-!
概要：P_Σ の元の Yoneda comma の反転を、同じ coslice の底変換へ同定する。
方針：元の局所添字の反転同型と底の宇宙反転同型を合成する。
規約：元の対象と底射影の全単体を厳密に保持する。
使われ方：元の P_Σ Yoneda の有限余積保存の切断判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind

/-- 概要：元の P_Σ Yoneda の反転を、小さい反転底の持ち上げから読む。
方針：底の宇宙反転同型と元の反転関手を合成する。
規約：元の Yoneda の作用を全高次で保持する。
使われ方：元の有限余積に双対な全有限積錐の像。 -/
def oppositeSigmaYoneda (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ (SigmaPresheafInfinity C).op :=
  (uliftOppositeIso C).hom ≫ SSet.opFunctor.map (sigmaYonedaInfinityMap C)

/-- 概要：同じ反転 comma の元の小さい反転底への射影。
方針：元の comma 射影を反転し、底の宇宙反転を正規化する。
規約：元の指定 P_Σ 対象を保持する。
使われ方：前層の小さい復元から coslice への切断比較。 -/
def oppositeSigmaLeftKanProjection {C : SSet.{u}} [Quasicategory C]
    (w : (SigmaPresheafInfinity C) _⦋0⦌) :
    (leftKanShape (sigmaYonedaInfinityMap C) w).op ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C.op :=
  SSet.opFunctor.map (leftKanProjection (sigmaYonedaInfinityMap C) w) ≫ (uliftOppositeIso C).inv

/-- 概要：元の反転 Yoneda comma 射影は左 fibration である。
方針：元の右 fibration の反転と底の宇宙反転同型を合成する。
規約：元の指定対象と射影を保持する。
使われ方：同じ全錐の切断制限による極限判定。 -/
instance oppositeSigmaLeftKanProjection_leftFibration {C : SSet.{u}} [Quasicategory C]
    (w : (SigmaPresheafInfinity C) _⦋0⦌) : LeftFibration (oppositeSigmaLeftKanProjection w) where
  mem := leftFibrations.comp_mem _ _
    (LeftFibration.mem (p := SSet.opFunctor.map (leftKanProjection (sigmaYonedaInfinityMap C) w)))
    (MorphismProperty.of_isIso leftFibrations (uliftOppositeIso C).inv)

/-- 概要：元の Yoneda comma と同じ coslice 底変換は反転後に厳密に同型。
方針：元の局所添字反転と、底変換の基底同型を合成する。
規約：同値な別の底変換ではなく元の引き戻しを使う。
使われ方：全係数での極限性を元の P_Σ の錐へ戻す。 -/
def sigmaCommaCoslicePullbackIso {C : SSet.{u}} [Quasicategory C]
    (w : (SigmaPresheafInfinity C) _⦋0⦌) :
    (leftKanShape (sigmaYonedaInfinityMap C) w).op ≅
      pullback (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)))
        (oppositeSigmaYoneda C) :=
  F1B.kanLeftKanShapeOpIso (sigmaYonedaInfinityMap C) w ≪≫
    pullbackRightBaseIso _ (SSet.opFunctor.map (sigmaYonedaInfinityMap C)) (uliftOppositeIso C)

/-- 概要：同じ coslice 底変換の同型は元の反転底射影を厳密に保つ。
方針：底変換の射影計算と局所添字反転の射影公式を合成する。
規約：元の小さい底の全写像を保持する。
使われ方：同じ全錐の切断制限の同値の移送。 -/
lemma sigmaCommaCoslicePullbackIso_projection {C : SSet.{u}} [Quasicategory C]
    (w : (SigmaPresheafInfinity C) _⦋0⦌) :
    (sigmaCommaCoslicePullbackIso w).hom ≫
      pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)))
        (oppositeSigmaYoneda C) = oppositeSigmaLeftKanProjection w := by
  dsimp only [sigmaCommaCoslicePullbackIso, Iso.trans_hom, oppositeSigmaYoneda,
    oppositeSigmaLeftKanProjection]
  rw [Category.assoc, pullbackRightBaseIso_hom_snd]
  rw [← Category.assoc, F1B.kanLeftKanShapeOpIso_projection]

end SerrePositivity.InfinityCategories.HomotopyLimits
