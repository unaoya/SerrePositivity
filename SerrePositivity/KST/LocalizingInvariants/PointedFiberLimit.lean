module

public import SerrePositivity.KST.Spectra.PointedFiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
概要：既存の点つき fiber とその包含の通常の引き戻し普遍性。
方針：零合成からの既存の持ち上げと包含による外延性を使う。
規約：段の fiber を別の選択された引き戻しへ置き換えない。
使われ方：実 BF fiber の全段の極限性からの ∞ 極限性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.FiberModel

lemma pointComposite_zero {A B : PointedSimplicialSet.{u}}
    (f : A ⟶ PointedObject.point.{u}) : f ≫ PointedObject.fromPoint B = 0 := by
  have h : PointedObject.fromPoint B = 0 := PointedObject.point_isZero.eq_of_src _ _
  rw [h, comp_zero]

/-- 元の実 fiber の包含と一点への射からなる引き戻し錐。 -/
def pointedCone {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    PullbackCone p (PointedObject.fromPoint B) :=
  PullbackCone.mk (pointedFiberι p) (PointedObject.toPoint (pointedFiber p))
    ((pointedFiberι_comp p).trans (pointComposite_zero _).symm)

/-- この錐は元の段の射を保つ通常の極限錐。 -/
def pointedCone_isLimit {E B : PointedSimplicialSet.{u}} (p : E ⟶ B) :
    IsLimit (pointedCone p) := by
  let lift (s : PullbackCone p (PointedObject.fromPoint B)) :=
    pointedFiberLiftOfZero p s.fst (s.condition.trans (pointComposite_zero s.snd))
  apply PullbackCone.IsLimit.mk _ lift
  · intro s
    exact pointedFiberLiftOfZero_ι p s.fst _
  · intro s
    exact PointedObject.point_isZero.eq_of_tgt _ _
  · intro s m hm _
    apply pointedFiber_hom_ext p
    exact hm.trans (pointedFiberLiftOfZero_ι p s.fst _).symm

end SerrePositivity.KST.LocalizingInvariants.FiberModel
