module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelArrow

/-!
概要：選んだ構造射との可換式を保つ底変換射の Cartesian 性と開包含性。
方針：元の pullback 正方形と段の pullback 正方形の貼り合わせを消去する。
規約：構造射は等しい合成への置換をせず保持する。
使われ方：G2 の後段の重なりと三重交叉の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S X Y : Scheme.{u}}

/-- 選んだ構造射との可換式で作る底変換射は、元の射の実際の底変換。 -/
theorem isPullback_baseChangedModelArrow (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    (l : X ⟶ Y) (hl : l ≫ q = p) :
    IsPullback (pullback.snd γ p) (baseChangedModelArrow γ p q l hl) l (pullback.snd γ q) := by
  have houter : IsPullback (pullback.snd γ p)
      (baseChangedModelArrow γ p q l hl ≫ pullback.fst γ q) (l ≫ q) γ := by
    rw [baseChangedModelArrow_fst, hl]
    exact (IsPullback.of_hasPullback γ p).flip
  exact houter.of_bot (baseChangedModelArrow_snd γ p q l hl).symm
    (IsPullback.of_hasPullback γ q).flip

/-- 選んだ構造射を保った底変換も、開包含を保存する。 -/
theorem isOpenImmersion_baseChangedModelArrow (γ : B ⟶ S) (p : X ⟶ S) (q : Y ⟶ S)
    (l : X ⟶ Y) (hl : l ≫ q = p) [IsOpenImmersion l] :
    IsOpenImmersion (baseChangedModelArrow γ p q l hl) :=
  MorphismProperty.of_isPullback (isPullback_baseChangedModelArrow γ p q l hl) inferInstance

end SerrePositivity.AlgebraicGeometry
