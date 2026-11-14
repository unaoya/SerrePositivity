module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapPrimitive
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.ComplexMappingCoconeMap

/-!
概要：実 cospan の模型射を、元の差の mapping cocone 射へ同定する。
方針：二脚と比較 cochain の三成分を計算し、元の複体同型と可換にする。
規約：三つの元の代数射を保持。使われ方：模型の準同型不変性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

lemma map_toMappingCocone : (map R f₀ g₀ f₁ g₁ a b c hf hg).hom ≫ toMappingCocone R f₁ g₁ =
    toMappingCocone R f₀ g₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R f₀ g₀)
      (difference R f₁ g₁) (sumMap R a c) b.hom (difference_comm R _ _ _ _ _ _ _ hf hg) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgMappingCocone_hom_ext (difference R f₁ g₁)
  · rw [Category.assoc, toMappingCocone_fst, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_fst, ← Category.assoc, toMappingCocone_fst]
    apply biprod.hom_ext
    · rw [Category.assoc, pairHom_fst, Category.assoc, sumMap, biprod.map_fst,
        ← Category.assoc, pairHom_fst]
      exact congrArg Mon.Hom.hom (map_left R _ _ _ _ _ _ _ _ _)
    · rw [Category.assoc, pairHom_snd, Category.assoc, sumMap, biprod.map_snd,
        ← Category.assoc, pairHom_snd]
      exact congrArg Mon.Hom.hom (map_right R _ _ _ _ _ _ _ _ _)
  · rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      toMappingCocone_snd, map_primitive]
    rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap_snd, ← Cochain.comp_assoc_of_first_is_zero_cochain,
      toMappingCocone_snd]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
