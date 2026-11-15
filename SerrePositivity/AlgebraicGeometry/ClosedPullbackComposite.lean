module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
概要：二段の底変換の実際の射と Cartesian 正方形を構成し、閉埋め込み性を移す。
方針：pullback の lift と Cartesian 正方形の横の貼り合わせの消去を用いる。
規約：合成 b=h≫g は指定した等式で照合する。
使われ方：C04 の極限の閉埋め込みを affine な標的開へ制限する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {X S T V : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (h : V ⟶ T)
  (b : V ⟶ S) (hb : h ≫ g = b)

/-- 合成に沿う底変換から、一段目の底変換への実際の射。 -/
def pullbackCompositeMap : pullback f b ⟶ pullback f g :=
  pullback.lift (pullback.fst f b) (pullback.snd f b ≫ h) (by
    rw [Category.assoc, hb, pullback.condition])

/-- 二段の底変換の比較と第二射影の正方形は Cartesian。 -/
theorem isPullback_pullbackCompositeMap :
    IsPullback (pullbackCompositeMap f g h b hb) (pullback.snd f b)
      (pullback.snd f g) h := by
  apply IsPullback.of_right ?_ (by simp [pullbackCompositeMap])
    (IsPullback.of_hasPullback f g)
  simpa only [pullbackCompositeMap, pullback.lift_fst, hb] using
    (IsPullback.of_hasPullback f b)

include h hb in
/-- 一段目の底変換の閉埋め込み性は、指定された合成への底変換でも保たれる。 -/
theorem isClosedImmersion_pullback_snd_of_composite
    [IsClosedImmersion (pullback.snd f g)] : IsClosedImmersion (pullback.snd f b) :=
  MorphismProperty.of_isPullback (isPullback_pullbackCompositeMap f g h b hb) inferInstance

end SerrePositivity.AlgebraicGeometry
