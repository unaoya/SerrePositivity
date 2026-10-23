module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SliceShapePushoutGluing
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：形状の pushout 上の錐全体を、二部分の錐の厳密な引き戻しとして表示する。
方針：任意パラメータの貼り合わせと一意性を引き戻しの普遍性に束ねる。
規約：元の全単体と図式を保持、単射性は不要。使われ方：固定頂点の錐空間の接着。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {A B C D X : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X)

/-- 全錐の空間は元の二部分の錐の空間の厳密な引き戻し。 -/
lemma sliceShapePushout_isPullback :
    IsPullback (sliceOverRestrict p i) (sliceOverRestrict p j)
      (sliceOverRestrict (i ≫ p) f)
      (normalizedConeRestriction (j ≫ p) g (conePushoutBoundary_eq hp p)) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (sliceShapePushout_comm hp p))
  apply PullbackCone.isLimitAux'
  intro s
  let h := sliceShapePushout_lift hp p s.fst s.snd s.condition
  exact ⟨h.choose, h.choose_spec.1.1, h.choose_spec.1.2,
    fun {_} h₁ h₂ ↦ h.choose_spec.2 _ ⟨h₁, h₂⟩⟩

/-- 元の全錐を、二部分の錐の実際の単体集合の引き戻しへ表示する同型。 -/
def sliceShapePushoutIso :
    sliceOver p ≅ pullback (sliceOverRestrict (i ≫ p) f)
      (normalizedConeRestriction (j ≫ p) g (conePushoutBoundary_eq hp p)) :=
  (sliceShapePushout_isPullback hp p).isoPullback

end SerrePositivity.InfinityCategories.F2
