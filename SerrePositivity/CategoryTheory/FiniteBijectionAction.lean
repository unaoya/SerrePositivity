module

public import SerrePositivity.CategoryTheory.FiniteBijection
public import Mathlib.CategoryTheory.Endomorphism

/-!
# 各濃度の対称群作用から全単射圏上の関手へ

対象の族と各段の対称群作用を、小さい有限全単射圏上の関手へまとめる。
等しい濃度の間の移送を明示し、骨格の対象の等式から関手性を証明する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.FiniteBijection

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- 全単射を、各段の作用と濃度の移送から得る射へ送る。 -/
def familyMap (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    {X Y : FiniteBijection} (f : X ⟶ Y) : A (card X) ⟶ A (card Y) :=
  (ρ (card X) ((equivOfHom f).trans (finCongr (card_eq_of_hom f).symm))).asIso.hom ≫
    eqToHom (congrArg A (card_eq_of_hom f))

/-- 恒等全単射は恒等射へ送られる。 -/
lemma familyMap_id (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    (X : FiniteBijection) : familyMap A ρ (𝟙 X) = 𝟙 (A (card X)) := by
  have h := congrArg (fun a : Aut (A (card X)) ↦ a.asIso.hom) ((ρ (card X)).map_one)
  simpa only [familyMap, equivOfHom_id, finCongr_refl, Equiv.trans_refl,
    eqToHom_refl, Category.comp_id, Aut.one_asIso, Iso.refl_hom, Aut.mul_asIso,
    Iso.trans_hom, Equiv.Perm.mul_def, Equiv.Perm.one_def] using h

/-- 全単射の合成は誘導射の合成へ送られる。 -/
lemma familyMap_comp (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n))
    {X Y Z : FiniteBijection} (f : X ⟶ Y) (g : Y ⟶ Z) :
    familyMap A ρ (f ≫ g) = familyMap A ρ f ≫ familyMap A ρ g := by
  cases object_eq_of_hom f
  cases object_eq_of_hom g
  have h := congrArg (fun a : Aut (A (card X)) ↦ a.asIso.hom)
    ((ρ (card X)).map_mul (equivOfHom g) (equivOfHom f))
  simpa only [familyMap, equivOfHom_comp, finCongr_refl, Equiv.trans_refl,
    eqToHom_refl, Category.comp_id, Aut.one_asIso, Iso.refl_hom, Aut.mul_asIso,
    Iso.trans_hom, Equiv.Perm.mul_def, Equiv.Perm.one_def] using h

/-- 各段の対称群作用を備えた対象の族を、全単射圏上の関手にする。 -/
def familyFunctor (A : ℕ → C) (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n)) :
    FiniteBijection ⥤ C where
  obj X := A (card X)
  map f := familyMap A ρ f
  map_id X := familyMap_id A ρ X
  map_comp f g := familyMap_comp A ρ f g

/-- 標準の置換の像は元の作用そのもの。 -/
lemma familyFunctor_map_permutation (A : ℕ → C)
    (ρ : ∀ n, Equiv.Perm (Fin n) →* Aut (A n)) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (familyFunctor A ρ).map (permutation n σ) = (ρ n σ).asIso.hom := by
  simp [familyFunctor, familyMap, permutation]

end SerrePositivity.FiniteBijection
