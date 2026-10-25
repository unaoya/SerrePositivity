module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConeEquiv

/-!
概要：全経路付き錐の表現を、実 cospan の変換と源の前合成に対して自然にする。
方針：二脚を後合成し、全経路を元の標的の経路関手で送って三成分を比較する。
規約：cospan の可換式は明示し、経路の選択を変更しない。
使われ方：Postnikov の実 class と cell class の同じ模型の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ W : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

def PathCone.map (s : PathCone R f₀ g₀ W) : PathCone R f₁ g₁ W where
  left := s.left ≫ a
  right := s.right ≫ c
  path := s.path ≫ Path.map R b
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc, s.source_eq,
      Category.assoc, ← hf, ← Category.assoc]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc, s.target_eq,
      Category.assoc, ← hg, ← Category.assoc]

lemma homPathCone_map (u : W ⟶ algebra R f₀ g₀) :
    homPathCone R f₁ g₁ (u ≫ map R f₀ g₀ f₁ g₁ a b c hf hg) =
      (homPathCone R f₀ g₀ u).map R f₀ g₀ f₁ g₁ a b c hf hg := by
  apply PathCone.ext R f₁ g₁
  · exact (Category.assoc _ _ _).trans
      (congrArg (u ≫ ·) (map_left R f₀ g₀ f₁ g₁ a b c hf hg)) |>.trans
      (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans
      (congrArg (u ≫ ·) (map_right R f₀ g₀ f₁ g₁ a b c hf hg)) |>.trans
      (Category.assoc _ _ _).symm
  · exact (Category.assoc _ _ _).trans
      (congrArg (u ≫ ·) (map_path R f₀ g₀ f₁ g₁ a b c hf hg)) |>.trans
      (Category.assoc _ _ _).symm

lemma pathConeLift_map (s : PathCone R f₀ g₀ W) :
    pathConeLift R f₁ g₁ (s.map R f₀ g₀ f₁ g₁ a b c hf hg) =
      pathConeLift R f₀ g₀ s ≫ map R f₀ g₀ f₁ g₁ a b c hf hg := by
  apply hom_ext R f₁ g₁
  · rw [pathConeLift_left, Category.assoc, map_left, ← Category.assoc, pathConeLift_left]
    rfl
  · rw [pathConeLift_right, Category.assoc, map_right, ← Category.assoc, pathConeLift_right]
    rfl
  · rw [pathConeLift_path, Category.assoc, map_path, ← Category.assoc, pathConeLift_path]
    rfl

lemma PathCone.map_precomp (s : PathCone R f₀ g₀ W) {V : Mon (Complex R)} (u : V ⟶ W) :
    (s.precomp R f₀ g₀ u).map R f₀ g₀ f₁ g₁ a b c hf hg =
      (s.map R f₀ g₀ f₁ g₁ a b c hf hg).precomp R f₁ g₁ u := by
  apply PathCone.ext R f₁ g₁ <;> exact Category.assoc _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
