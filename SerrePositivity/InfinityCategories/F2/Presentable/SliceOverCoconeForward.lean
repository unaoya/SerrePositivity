module

public import SerrePositivity.InfinityCategories.F2.Presentable.JoinAssociatorOuterInclusions
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.Cocone

/-!
概要：対象上の図式の余錐を、底の余錐圏の同じ増大余錐上の射へ比較する。
方針：二重 join の結合同型を curry し、元の増大図式を固定する。
規約：元の全図式と対象への射を厳密に保持する。
使われ方：対象上の余錐の普遍性を底の余錐の始対象性から検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {K X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x)

/-- 概要：対象上の図式そのものを底の増大余錐として読む。
方針：slice の uncurry を使う。
規約：元の対象への全高次単体を含む。
使われ方：二重 slice 比較の固定標的。 -/
def sliceOverAugmentationCocone : (sliceUnder (a ≫ sliceOverProjection x)) _⦋0⦌ :=
  ⟨sliceOverUncurry a, sliceOverUncurry_projection a⟩

/-- 概要：対象上の普遍余錐を二重 join の逆結合で組み替えた全射。
方針：二回 uncurry して逆結合同型で前合成する。
規約：余錐圏自体を全パラメーターとして保持する。
使われ方：元の余錐圏からの比較射。 -/
def sliceOverCoconeForwardDiagram :
    join K (join (sliceUnder a) Δ[0]) ⟶ X :=
  (stableJoinAssociator K (sliceUnder a) Δ[0]).inv ≫
    sliceOverUncurry (sliceUnderUncurry (𝟙 (sliceUnder a)))

/-- 概要：組み替えた全射は底の元の図式に一致する。
方針：左端包含の公式と二つの uncurry 射影則を使う。
規約：底の全図式の等式。
使われ方：底の余錐圏への curry の固定条件。 -/
lemma sliceOverCoconeForwardDiagram_fixed :
    joinInl K (join (sliceUnder a) Δ[0]) ≫ sliceOverCoconeForwardDiagram x a =
      a ≫ sliceOverProjection x := by
  rw [sliceOverCoconeForwardDiagram, ← Category.assoc, joinAssociator_leftmost_inv,
    Category.assoc, sliceOverUncurry_projection, ← Category.assoc,
    sliceUnderUncurry_fixed]

/-- 概要：右端の点への制限は元の増大余錐そのもの。
方針：逆結合同型の中間包含則と curry の固定条件を使う。
規約：元の対象上の全図式を厳密に回収する。
使われ方：底の余錐圏の固定標的への slice 比較。 -/
lemma sliceOverCoconeForwardDiagram_right :
    joinMap (𝟙 K) (joinInr (sliceUnder a) Δ[0]) ≫
      sliceOverCoconeForwardDiagram x a = (sliceOverAugmentationCocone x a).val := by
  rw [sliceOverCoconeForwardDiagram, ← Category.assoc, stableJoinAssociator_middle_inv,
    ← sliceOverUncurry_precomp, sliceUnderUncurry_fixed]
  rfl

/-- 概要：対象上の余錐圏から、底の余錐圏内の元の増大余錐上の slice への比較射。
方針：組み替えた普遍全射を二回 curry する。
規約：固定標的は元の全増大余錐。
使われ方：底の余極限性から対象上の余極限性への移送。 -/
def sliceOverCoconeForward : sliceUnder a ⟶
    sliceOver (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a)) :=
  sliceOverCurry
    (sliceUnderCurry (sliceOverCoconeForwardDiagram x a)
      (sliceOverCoconeForwardDiagram_fixed x a)) (by
        apply sliceUnderUncurry_injective (a ≫ sliceOverProjection x)
        rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry,
          sliceUnderUncurry_yoneda]
        exact sliceOverCoconeForwardDiagram_right x a)

/-- 概要：比較射の二回の uncurry は組み替えた普遍全射。
方針：二つの curry の逆則を使う。
規約：全パラメーターの等式。
使われ方：比較射の逆と全自然な同定の構成。 -/
lemma sliceOverCoconeForward_uncurry :
    sliceUnderUncurry (sliceOverUncurry (sliceOverCoconeForward x a)) =
      sliceOverCoconeForwardDiagram x a := by
  rw [sliceOverCoconeForward, sliceOverUncurry_curry, sliceUnderUncurry_curry]

end SerrePositivity.InfinityCategories.F2.Presentable
