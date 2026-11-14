module

public import SerrePositivity.AlgebraicGeometry.ProperInductiveLevelZeroBaseChange
public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
概要：帰納的レベルの閉中心上の射と、任意の底変換の Cartesian 比較。
方針：イデアル層の comapIso と二つの pullback 正方形の貼り合わせを使う。
規約：中心の被約化も底変換の平坦性も仮定しない。
使われ方：G3 の正段の底変換の帰納仮定への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X Y T : Scheme.{u}}

/-- 逆像中心から元の中心への実際の射。 -/
def inductiveCenterBaseChangeProjection (J : Y.IdealSheafData) (h : T ⟶ Y) :
    (J.comap h).subscheme ⟶ J.subscheme :=
  (J.comapIso h).hom ≫ pullback.snd h J.subschemeι

/-- 逆像中心は元の中心の Cartesian な底変換。 -/
theorem isPullback_inductiveCenterBaseChangeProjection (J : Y.IdealSheafData) (h : T ⟶ Y) :
    IsPullback (J.comap h).subschemeι (inductiveCenterBaseChangeProjection J h)
      h J.subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (J.comapIso h) (by simp) rfl
  dsimp [inductiveCenterBaseChangeProjection]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, J.comapIso_hom_fst]

/-- 底変換した射の逆像中心上の対象から、元の中心上の対象への射。 -/
def inductiveCenterRestrictionBaseChangeMap (r : X ⟶ Y) (h : T ⟶ Y)
    (J : Y.IdealSheafData) :
    pullback (pullback.snd r h) (J.comap h).subschemeι ⟶ pullback r J.subschemeι :=
  pullback.lift
    (pullback.fst (pullback.snd r h) (J.comap h).subschemeι ≫ pullback.fst r h)
    (pullback.snd (pullback.snd r h) (J.comap h).subschemeι ≫
      inductiveCenterBaseChangeProjection J h) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, (isPullback_inductiveCenterBaseChangeProjection J h).w]
    simp only [Category.assoc])

/-- 中心上の新しい射は、元の中心上の射の実際の底変換。 -/
theorem isPullback_inductiveCenterRestrictionBaseChangeMap
    (r : X ⟶ Y) (h : T ⟶ Y) (J : Y.IdealSheafData) :
    IsPullback (inductiveCenterRestrictionBaseChangeMap r h J)
      (pullback.snd (pullback.snd r h) (J.comap h).subschemeι)
      (pullback.snd r J.subschemeι) (inductiveCenterBaseChangeProjection J h) := by
  have H := (IsPullback.of_hasPullback (pullback.snd r h) (J.comap h).subschemeι).paste_horiz
    (IsPullback.of_hasPullback r h)
  have H' : IsPullback
      (inductiveCenterRestrictionBaseChangeMap r h J ≫ pullback.fst r J.subschemeι)
      (pullback.snd (pullback.snd r h) (J.comap h).subschemeι) r
      (inductiveCenterBaseChangeProjection J h ≫ J.subschemeι) := by
    simpa only [inductiveCenterRestrictionBaseChangeMap, pullback.lift_fst,
      (isPullback_inductiveCenterBaseChangeProjection J h).w] using H
  exact H'.of_right (by simp [inductiveCenterRestrictionBaseChangeMap])
    (IsPullback.of_hasPullback r J.subschemeι)

end SerrePositivity.AlgebraicGeometry
