module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapQuasiIso

/-!
概要：実 cospan 射の厳密 pullback 射と、経路模型への元の比較の自然性を構成する。
方針：元の二射影で持ち上げ、二脚と定数経路の共同単射性で比較する。
規約：全て実代数射で、元の二脚を保持。使われ方：相対拡大の絶対模型との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PullbackMap
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

def map : MonoidPullback.obj f₀ g₀ ⟶ MonoidPullback.obj f₁ g₁ :=
  MonoidPullback.lift f₁ g₁ (MonoidPullback.fst f₀ g₀ ≫ a) (MonoidPullback.snd f₀ g₀ ≫ c)
    (by rw [Category.assoc, hf, ← Category.assoc, MonoidPullback.condition,
      Category.assoc, ← hg, ← Category.assoc])

lemma map_fst : map R f₀ g₀ f₁ g₁ a b c hf hg ≫ MonoidPullback.fst f₁ g₁ =
    MonoidPullback.fst f₀ g₀ ≫ a := MonoidPullback.lift_fst _ _ _ _ _

lemma map_snd : map R f₀ g₀ f₁ g₁ a b c hf hg ≫ MonoidPullback.snd f₁ g₁ =
    MonoidPullback.snd f₀ g₀ ≫ c := MonoidPullback.lift_snd _ _ _ _ _

lemma comparison_naturality : HomotopyPullbackModel.comparison R f₀ g₀ ≫
    HomotopyPullbackModel.map R f₀ g₀ f₁ g₁ a b c hf hg =
      map R f₀ g₀ f₁ g₁ a b c hf hg ≫ HomotopyPullbackModel.comparison R f₁ g₁ := by
  apply HomotopyPullbackModel.hom_ext R f₁ g₁
  · rw [Category.assoc, HomotopyPullbackModel.map_left, ← Category.assoc,
      HomotopyPullbackModel.comparison_left, Category.assoc,
      HomotopyPullbackModel.comparison_left, map_fst]
  · rw [Category.assoc, HomotopyPullbackModel.map_right, ← Category.assoc,
      HomotopyPullbackModel.comparison_right, Category.assoc,
      HomotopyPullbackModel.comparison_right, map_snd]
  · calc
      _ = (MonoidPullback.fst f₀ g₀ ≫ f₀ ≫ Path.diagonal R B₀) ≫ Path.map R b := by
        rw [Category.assoc, HomotopyPullbackModel.map_path, ← Category.assoc,
          HomotopyPullbackModel.comparison_path]
      _ = MonoidPullback.fst f₀ g₀ ≫ (f₀ ≫ b) ≫ Path.diagonal R B₁ := by
        simp only [Category.assoc, Path.diagonal_naturality]
      _ = MonoidPullback.fst f₀ g₀ ≫ (a ≫ f₁) ≫ Path.diagonal R B₁ := by rw [hf]
      _ = (MonoidPullback.fst f₀ g₀ ≫ a) ≫ f₁ ≫ Path.diagonal R B₁ := by
        simp only [Category.assoc]
      _ = (map R f₀ g₀ f₁ g₁ a b c hf hg ≫ MonoidPullback.fst f₁ g₁) ≫
          f₁ ≫ Path.diagonal R B₁ := by rw [map_fst]
      _ = _ := by
        symm
        rw [Category.assoc, HomotopyPullbackModel.comparison_path]
        simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PullbackMap
