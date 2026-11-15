module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：同じ基底射に関する二つの Cartesian な正方形から、ファイバー積の Cartesian 比較を作る。
方針：二つの正方形の lift を組み合わせ、ファイバー積の普遍性を直接確認する。
規約：底変換と有限極限の法則。
使われ方：G2 の元の三重交叉と模型の三重交叉の実際の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {B S X₁ X₂ Y₁ Y₂ : C}
  (f₁ : X₁ ⟶ B) (f₂ : X₂ ⟶ B) (g₁ : Y₁ ⟶ S) (g₂ : Y₂ ⟶ S)
  (w : B ⟶ S) (a₁ : X₁ ⟶ Y₁) (a₂ : X₂ ⟶ Y₂)
  (h₁ : IsPullback a₁ f₁ g₁ w) (h₂ : IsPullback a₂ f₂ g₂ w)

include h₁ h₂

/-- 同じ基底射に関する二つの Cartesian な比較から、実際のファイバー積の射を作る。 -/
def cartesianPullbackMap : pullback f₁ f₂ ⟶ pullback g₁ g₂ :=
  pullback.map f₁ f₂ g₁ g₂ a₁ a₂ w h₁.w.symm h₂.w.symm

/-- ファイバー積の比較の pullback cone への実際の lift。 -/
def cartesianPullbackLift (s : PullbackCone (pullback.fst g₁ g₂ ≫ g₁) w) :
    s.pt ⟶ pullback f₁ f₂ := by
  have hs₁ : (s.fst ≫ pullback.fst g₁ g₂) ≫ g₁ = s.snd ≫ w := by
    simpa only [Category.assoc] using s.condition
  have hs₂ : (s.fst ≫ pullback.snd g₁ g₂) ≫ g₂ = s.snd ≫ w := by
    simpa only [Category.assoc, pullback.condition] using s.condition
  exact pullback.lift (h₁.lift _ _ hs₁) (h₂.lift _ _ hs₂) (by simp)

/-- 比較 cone への lift の模型側の合成式。 -/
theorem cartesianPullbackLift_map (s : PullbackCone (pullback.fst g₁ g₂ ≫ g₁) w) :
    cartesianPullbackLift f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂ s ≫
      cartesianPullbackMap f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂ = s.fst := by
  apply pullback.hom_ext <;> simp [cartesianPullbackLift, cartesianPullbackMap, Category.assoc]

/-- 比較 cone への lift の基底側の合成式。 -/
theorem cartesianPullbackLift_base (s : PullbackCone (pullback.fst g₁ g₂ ≫ g₁) w) :
    cartesianPullbackLift f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂ s ≫ pullback.fst f₁ f₂ ≫ f₁ = s.snd := by
  simp [cartesianPullbackLift, Category.assoc]

/-- 二つの Cartesian な正方形のファイバー積の比較も、同じ基底射の底変換。 -/
theorem isPullback_cartesianPullbackMap :
    IsPullback (cartesianPullbackMap f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂)
      (pullback.fst f₁ f₂ ≫ f₁) (pullback.fst g₁ g₂ ≫ g₁) w := by
  refine ⟨?_, ⟨PullbackCone.IsLimit.mk _
    (cartesianPullbackLift f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂) ?_ ?_ ?_⟩⟩
  · simp [cartesianPullbackMap, Category.assoc, h₁.w]
  · intro s
    exact cartesianPullbackLift_map f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂ s
  · intro s
    exact cartesianPullbackLift_base f₁ f₂ g₁ g₂ w a₁ a₂ h₁ h₂ s
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · apply h₁.hom_ext
      · simpa [cartesianPullbackLift, cartesianPullbackMap, Category.assoc] using
          congrArg (fun z ↦ z ≫ pullback.fst g₁ g₂) hm₁
      · simpa [cartesianPullbackLift, Category.assoc] using hm₂
    · apply h₂.hom_ext
      · simpa [cartesianPullbackLift, cartesianPullbackMap, Category.assoc] using
          congrArg (fun z ↦ z ≫ pullback.snd g₁ g₂) hm₁
      · simpa [cartesianPullbackLift, Category.assoc, pullback.condition] using hm₂

end SerrePositivity.AlgebraicGeometry
