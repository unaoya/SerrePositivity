module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapCocone
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackFunctor
public import SerrePositivity.KST.LocalizingInvariants.CochainBiprodQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainMappingCoconeMapQuasiIso

/-!
概要：実 cospan の三成分の準同型は、元の経路模型の実比較射でも準同型になる。
方針：元の差の mapping cocone 射と可換な複体同型を使い、準同型性を移す。
規約：成分ごとの準同型性を証明して使う。使われ方：LT の底の準同型比較の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A₀ B₀ C₀ A₁ B₁ C₁ : Mon (Complex R)}
  (f₀ : A₀ ⟶ B₀) (g₀ : C₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) (g₁ : C₁ ⟶ B₁)
  (a : A₀ ⟶ A₁) (b : B₀ ⟶ B₁) (c : C₀ ⟶ C₁)
  (hf : a ≫ f₁ = f₀ ≫ b) (hg : c ≫ g₁ = g₀ ≫ b)

lemma map_quasiIso (ha : QuasiIso a.hom) (hb : QuasiIso b.hom) (hc : QuasiIso c.hom) :
    QuasiIso (map R f₀ g₀ f₁ g₁ a b c hf hg).hom := by
  have hs : QuasiIso (sumMap R a c) := cochainBiprodMap_quasiIso a.hom c.hom ha hc
  have hm : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (difference R f₀ g₀) (difference R f₁ g₁)
      (sumMap R a c) b.hom (difference_comm R _ _ _ _ _ _ _ hf hg)) :=
    cochainMappingCoconeMap_quasiIso _ _ _ _ _ hs hb
  have ht : QuasiIso ((map R f₀ g₀ f₁ g₁ a b c hf hg).hom ≫ toMappingCocone R f₁ g₁) := by
    rw [map_toMappingCocone]
    exact quasiIso_comp _ _ (hφ := quasiIso_of_isIso (complexIso R f₀ g₀).hom) (hφ' := hm)
  have : QuasiIso (toMappingCocone R f₁ g₁) := quasiIso_of_isIso (complexIso R f₁ g₁).hom
  exact quasiIso_of_comp_right (map R f₀ g₀ f₁ g₁ a b c hf hg).hom (toMappingCocone R f₁ g₁)

lemma diagramMap_quasiIso {D E : WalkingCospan ⥤ Mon (Complex R)} (α : D ⟶ E)
    (h : ∀ j, QuasiIso (α.app j).hom) : QuasiIso (diagramMap R α).hom :=
  map_quasiIso R _ _ _ _ _ _ _ _ _ (h .left) (h .one) (h .right)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
