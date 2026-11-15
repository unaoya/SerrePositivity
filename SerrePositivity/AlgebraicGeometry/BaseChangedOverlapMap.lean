module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
概要：係数段の底変換模型の間の開包含を、実際の射と Cartesian 正方形として保つ。
方針：pullback lift の二射影の式と Cartesian 正方形の貼り合わせの消去。
規約：係数段の射に平坦性・単射性を要求しない。
使われ方：G2 の有限段の gluing datum の重なりの開包含。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S U V : Scheme.{u}}

/-- 同じ係数段へ移した二つの模型の間の実際の射。 -/
def baseChangedOverlapMap (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) :
    pullback γ (q ≫ p) ⟶ pullback γ p :=
  pullback.lift (pullback.fst γ (q ≫ p)) (pullback.snd γ (q ≫ p) ≫ q)
    (by simpa only [Category.assoc] using (pullback.condition (f := γ) (g := q ≫ p)))

/-- 段の基底座標を保つ。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapMap_fst (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) :
    baseChangedOverlapMap γ p q ≫ pullback.fst γ p = pullback.fst γ (q ≫ p) := by
  simp [baseChangedOverlapMap]

/-- 固定模型への射影は元の射 q と可換。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapMap_snd (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) :
    baseChangedOverlapMap γ p q ≫ pullback.snd γ p = pullback.snd γ (q ≫ p) ≫ q := by
  simp [baseChangedOverlapMap]

/-- 段の模型間の射は元の射の実際の底変換。 -/
theorem isPullback_baseChangedOverlapMap (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) :
    IsPullback (pullback.snd γ (q ≫ p)) (baseChangedOverlapMap γ p q)
      q (pullback.snd γ p) := by
  have houter : IsPullback (pullback.snd γ (q ≫ p))
      (baseChangedOverlapMap γ p q ≫ pullback.fst γ p) (q ≫ p) γ := by
    rw [baseChangedOverlapMap_fst]
    exact (IsPullback.of_hasPullback γ (q ≫ p)).flip
  exact houter.of_bot (baseChangedOverlapMap_snd γ p q).symm
    (IsPullback.of_hasPullback γ p).flip

/-- 模型間の開包含は同じ係数段への底変換後にも開包含。 -/
theorem isOpenImmersion_baseChangedOverlapMap (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U)
    [IsOpenImmersion q] : IsOpenImmersion (baseChangedOverlapMap γ p q) :=
  MorphismProperty.of_isPullback (isPullback_baseChangedOverlapMap γ p q) inferInstance

end SerrePositivity.AlgebraicGeometry
