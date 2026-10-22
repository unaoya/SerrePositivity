module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：実 cospan の可換な三つの代数射から、元の経路模型の実代数射を構成する。
方針：乗法的経路を標的の射で後合成し、指定二脚とともに普遍 lift へ渡す。
規約：二脚と経路を厳密に保持。使われ方：係数像への制限による拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

def mapWitness : Path.Witness R ((left R f₀ g₀ ≫ a) ≫ f₁)
    ((right R f₀ g₀ ≫ c) ≫ g₁) where
  hom := path R f₀ g₀ ≫ Path.map R b
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc, path_source,
      Category.assoc, Category.assoc, hf]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc, path_target,
      Category.assoc, Category.assoc, hg]

def map : algebra R f₀ g₀ ⟶ algebra R f₁ g₁ :=
  lift R f₁ g₁ (left R f₀ g₀ ≫ a) (right R f₀ g₀ ≫ c)
    (mapWitness R f₀ g₀ f₁ g₁ a b c hf hg)

lemma map_left : map R f₀ g₀ f₁ g₁ a b c hf hg ≫ left R f₁ g₁ = left R f₀ g₀ ≫ a :=
  lift_left R _ _ _ _ _

lemma map_right : map R f₀ g₀ f₁ g₁ a b c hf hg ≫ right R f₁ g₁ = right R f₀ g₀ ≫ c :=
  lift_right R _ _ _ _ _

lemma map_path : map R f₀ g₀ f₁ g₁ a b c hf hg ≫ path R f₁ g₁ =
    path R f₀ g₀ ≫ Path.map R b := lift_path R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
