module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：二つの単体的ホモトピー同値の積は、元の積射のホモトピー同値。
方針：両方の実ホモトピーを同じ時間変数で動かし、二つの逆を積にする。
規約：Kan 性やモデル構造は不要。使われ方：Tamme の写像空間比較の入力の積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
namespace TensorHomotopy

def leftShape (A B : SSet.{u}) : (A ⊗ B) ⊗ (Δ[1] : SSet.{u}) ⟶ A ⊗ Δ[1] where
  app _ := ↾fun p ↦ (p.1.1, p.2)
  naturality {_ _} _ := rfl

def rightShape (A B : SSet.{u}) : (A ⊗ B) ⊗ (Δ[1] : SSet.{u}) ⟶ B ⊗ Δ[1] where
  app _ := ↾fun p ↦ (p.1.2, p.2)
  naturality {_ _} _ := rfl

lemma leftShape_zero (A B : SSet.{u}) :
    SSet.ι₀ ≫ leftShape A B = fst A B ≫ SSet.ι₀ := rfl

lemma leftShape_one (A B : SSet.{u}) :
    SSet.ι₁ ≫ leftShape A B = fst A B ≫ SSet.ι₁ := rfl

lemma rightShape_zero (A B : SSet.{u}) :
    SSet.ι₀ ≫ rightShape A B = snd A B ≫ SSet.ι₀ := rfl

lemma rightShape_one (A B : SSet.{u}) :
    SSet.ι₁ ≫ rightShape A B = snd A B ≫ SSet.ι₁ := rfl

/-- 二つのホモトピーを同じ時間変数で動かす積ホモトピー。 -/
def tensor {A B X Y : SSet.{u}} {f₀ f₁ : A ⟶ X} {g₀ g₁ : B ⟶ Y}
    (H : SSet.Homotopy f₀ f₁) (K : SSet.Homotopy g₀ g₁) :
    SSet.Homotopy (f₀ ⊗ₘ g₀) (f₁ ⊗ₘ g₁) where
  h := lift (leftShape A B ≫ H.h) (rightShape A B ≫ K.h)
  h₀ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← Category.assoc, leftShape_zero,
        Category.assoc, H.h₀]
      rfl
    · rw [Category.assoc, lift_snd, ← Category.assoc, rightShape_zero,
        Category.assoc, K.h₀]
      rfl
  h₁ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← Category.assoc, leftShape_one,
        Category.assoc, H.h₁]
      rfl
    · rw [Category.assoc, lift_snd, ← Category.assoc, rightShape_one,
        Category.assoc, K.h₁]
      rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact z.1.property.elim

end TensorHomotopy

lemma tensor_simplicialHomotopyEquivalence {A B X Y : SSet.{u}}
    {f : A ⟶ X} {g : B ⟶ Y} (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ⊗ₘ g) := by
  obtain ⟨f', ⟨H₀⟩, ⟨H₁⟩⟩ := hf
  obtain ⟨g', ⟨K₀⟩, ⟨K₁⟩⟩ := hg
  refine ⟨f' ⊗ₘ g', ?_, ?_⟩
  · simpa only [← tensorHom_comp_tensorHom, id_tensorHom_id] using
      (⟨TensorHomotopy.tensor H₀ K₀⟩ : Nonempty (SSet.Homotopy _ _))
  · simpa only [← tensorHom_comp_tensorHom, id_tensorHom_id] using
      (⟨TensorHomotopy.tensor H₁ K₁⟩ : Nonempty (SSet.Homotopy _ _))

end SerrePositivity.KST.LocalizingInvariants
