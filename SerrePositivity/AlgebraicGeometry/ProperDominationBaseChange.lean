module

public import SerrePositivity.AlgebraicGeometry.ProperDominationDescent
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：固有支配と周辺を二段に底変換し、元の支配の実際の底変換と結び付ける。
方針：Cartesian 正方形の貼り合わせと消去を使う。
規約：忠実平坦性や模型の存在を追加仮定にしない。
使われ方：B01・B02 の一般の固有性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {T X P S B : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ X)
  (t : T ⟶ P) (q : P ⟶ S) (hcomm : t ≫ q = h ≫ f) (g : B ⟶ S)
include hcomm

/-- 周辺への射の二段の底変換は、元の構造射の底変換。 -/
theorem isPullback_dominationBaseChangeSource :
    IsPullback (pullback.snd (pullback.snd g q) t)
      (pullback.fst (pullback.snd g q) t ≫ pullback.fst g q) (h ≫ f) g := by
  simpa only [hcomm] using
    ((IsPullback.of_hasPullback (pullback.snd g q) t).flip.paste_vert
      (IsPullback.of_hasPullback g q).flip)

/-- 周辺を通る二段の底変換から、元の対象の底変換への実際の支配射。 -/
def dominationBaseChangeMap :
    pullback (pullback.snd g q) t ⟶ pullback g f :=
  pullback.lift (pullback.fst (pullback.snd g q) t ≫ pullback.fst g q)
    (pullback.snd (pullback.snd g q) t ≫ h) (by
      simpa only [Category.assoc] using
        (isPullback_dominationBaseChangeSource f h t q hcomm g).w.symm)

/-- 実際の二段の支配射は、元の支配射の底変換。 -/
theorem isPullback_dominationBaseChangeMap :
    IsPullback (pullback.snd (pullback.snd g q) t)
      (dominationBaseChangeMap f h t q hcomm g) h (pullback.snd g f) := by
  apply IsPullback.of_bot ?_ (by simp [dominationBaseChangeMap])
    (IsPullback.of_hasPullback g f).flip
  simpa only [dominationBaseChangeMap, pullback.lift_fst] using
    isPullback_dominationBaseChangeSource f h t q hcomm g

/-- 二段の模型からの実際の支配射は、固有性を保つ。 -/
theorem isProper_dominationBaseChangeMap [IsProper h] :
    IsProper (dominationBaseChangeMap f h t q hcomm g) :=
  MorphismProperty.of_isPullback
    (isPullback_dominationBaseChangeMap f h t q hcomm g) inferInstance

/-- 二段の模型からの実際の支配射は、全射性を保つ。 -/
theorem surjective_dominationBaseChangeMap [Surjective h] :
    Surjective (dominationBaseChangeMap f h t q hcomm g) :=
  MorphismProperty.of_isPullback
    (isPullback_dominationBaseChangeMap f h t q hcomm g) inferInstance

/-- 周辺の底変換への射影が閉埋め込みなら、同じ段の元の射は固有。 -/
theorem isProper_pullback_fst_of_closed_domination
    [IsSeparated f] [LocallyOfFiniteType f] [Surjective h] [IsProper q]
    [IsClosedImmersion (pullback.fst (pullback.snd g q) t)] :
    IsProper (pullback.fst g f) := by
  let a := dominationBaseChangeMap f h t q hcomm g
  haveI : Surjective a := surjective_dominationBaseChangeMap f h t q hcomm g
  haveI : IsProper (a ≫ pullback.fst g f) := by
    dsimp [a, dominationBaseChangeMap]
    rw [pullback.lift_fst]
    infer_instance
  exact isProper_of_proper_surjective_comp a (pullback.fst g f)

/-- 元の射が底変換後に固有なら、周辺への immersion の同じ底変換は閉埋め込み。 -/
theorem isClosedImmersion_dominationBaseChangeProjection
    [IsProper h] [IsImmersion t] [IsProper q] [IsProper (pullback.fst g f)] :
    IsClosedImmersion (pullback.fst (pullback.snd g q) t) := by
  let a := dominationBaseChangeMap f h t q hcomm g
  haveI : IsProper a := isProper_dominationBaseChangeMap f h t q hcomm g
  haveI : IsProper ((pullback.fst (pullback.snd g q) t) ≫ pullback.fst g q) := by
    have hh : a ≫ pullback.fst g f =
        pullback.fst (pullback.snd g q) t ≫ pullback.fst g q := by
      simp [a, dominationBaseChangeMap]
    rw [← hh]
    infer_instance
  exact isClosedImmersion_of_proper_over_base
    (pullback.fst (pullback.snd g q) t) (pullback.fst g q)

end SerrePositivity.AlgebraicGeometry
