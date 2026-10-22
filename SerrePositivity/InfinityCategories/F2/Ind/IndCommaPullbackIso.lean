module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteIndCommaSections
public import SerrePositivity.InfinityCategories.F2.Ind.PullbackRightBaseIso
public import SerrePositivity.InfinityCategories.F1B.KanLeftKanShapeCommaProjection

/-!
概要：実際の Ind Yoneda comma の反転を、同じ頂点の coslice の厳密な底変換へ同定する。
方針：既存の局所添字の反転同型と、元の底の宇宙反転同型を合成する。
規約：元の底射影を厳密に保持。使われ方：全係数の native 極限判定への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]

/-- 元の Yoneda を反転し、元の小さい反転底の持ち上げから読む。 -/
def oppositeIndYoneda : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ (IndInfinity κ C).op :=
  (uliftOppositeIso C).hom ≫ SSet.opFunctor.map (indYoneda κ C)

/-- 元の反転 comma と、同じ coslice の元の反転 Yoneda に沿う底変換の厳密な同型。 -/
def indCommaCoslicePullbackIso (w : (IndInfinity κ C) _⦋0⦌) :
    (leftKanShape (indYoneda κ C) w).op ≅
      pullback (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)))
        (oppositeIndYoneda κ) :=
  F1B.kanLeftKanShapeOpIso (indYoneda κ C) w ≪≫
    pullbackRightBaseIso _ (SSet.opFunctor.map (indYoneda κ C)) (uliftOppositeIso C)

/-- 同じ引き戻し同型は、元の正規化した反転底射影を厳密に保つ。 -/
lemma indCommaCoslicePullbackIso_projection (w : (IndInfinity κ C) _⦋0⦌) :
    (indCommaCoslicePullbackIso κ w).hom ≫
      pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)))
        (oppositeIndYoneda κ) = oppositeIndLeftKanProjection κ w := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w))
  let y := SSet.opFunctor.map (indYoneda κ C)
  change ((F1B.kanLeftKanShapeOpIso (indYoneda κ C) w).hom ≫
    (pullbackRightBaseIso p y (uliftOppositeIso C)).hom) ≫
      pullback.snd p ((uliftOppositeIso C).hom ≫ y) = _
  rw [Category.assoc, pullbackRightBaseIso_hom_snd p y (uliftOppositeIso C)]
  have h := F1B.kanLeftKanShapeOpIso_projection (indYoneda κ C) w
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ (uliftOppositeIso C).inv) h)

end SerrePositivity.InfinityCategories.F2.Ind
