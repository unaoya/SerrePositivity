module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackCoconeIso

/-!
概要：cospan の元の三つの射が誘導する模型射は比較 cochain も保持する。
方針：実乗法的経路の自然性と、経路関手の比較 cochain の自然性を合成する。
規約：指定した同じ模型射での等式。使われ方：cospan の準同型置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

lemma map_primitive : (Cochain.ofHom (map R f₀ g₀ f₁ g₁ a b c hf hg).hom).comp
    (primitive R f₁ g₁) (zero_add (-1)) =
      (primitive R f₀ g₀).comp (Cochain.ofHom b.hom) (add_zero (-1)) := by
  change (Cochain.ofHom (map R f₀ g₀ f₁ g₁ a b c hf hg).hom).comp
    ((Cochain.ofHom (path R f₁ g₁).hom).comp (Path.primitive R B₁) _) _ = _
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
  have hp : (map R f₀ g₀ f₁ g₁ a b c hf hg).hom ≫ (path R f₁ g₁).hom =
      (path R f₀ g₀).hom ≫ (Path.map R b).hom :=
    congrArg Mon.Hom.hom (map_path R f₀ g₀ f₁ g₁ a b c hf hg)
  rw [hp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
  change (Cochain.ofHom (path R f₀ g₀).hom).comp
    ((Cochain.ofHom (Path.mapHom R b)).comp (Path.primitive R B₁) _) _ = _
  rw [Path.mapHom_primitive, ← Cochain.comp_assoc_of_first_is_zero_cochain]
  rfl

def sumMap : A₀.X ⊞ C₀.X ⟶ A₁.X ⊞ C₁.X := biprod.map a.hom c.hom

include hf hg in
lemma difference_comm : difference R f₀ g₀ ≫ b.hom = sumMap R a c ≫ difference R f₁ g₁ := by
  have hf' : a.hom ≫ f₁.hom = f₀.hom ≫ b.hom := congrArg Mon.Hom.hom hf
  have hg' : c.hom ≫ g₁.hom = g₀.hom ≫ b.hom := congrArg Mon.Hom.hom hg
  change biprod.desc f₀.hom (-g₀.hom) ≫ b.hom =
    biprod.map a.hom c.hom ≫ biprod.desc f₁.hom (-g₁.hom)
  apply biprod.hom_ext'
  · simp only [← Category.assoc, biprod.inl_desc, biprod.inl_map]
    rw [Category.assoc, biprod.inl_desc]
    exact hf'.symm
  · simp only [← Category.assoc, biprod.inr_desc, biprod.inr_map]
    rw [Category.assoc, biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg]
    exact congrArg Neg.neg hg'.symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
