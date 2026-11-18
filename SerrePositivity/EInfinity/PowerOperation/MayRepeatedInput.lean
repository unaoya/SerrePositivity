module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionZero
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitPowers
public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.PairingRepresentatives

/-!
# May の D₀ の対角入力と二項作用への代入

May, Proposition 2.3(iii) の零次計算の補助。
単位からの同じ射を全入力に入れ、BE の部分合成を反復積の入力へ移す。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {X : C}

/-- 同じ単位からの射を、右に括った全テンソル入力へ入れる。 -/
def repeatedUnitInput (f : 𝟙_ C ⟶ X) : ∀ n : ℕ, 𝟙_ C ⟶ power X n
  | 0 => 𝟙 _
  | n + 1 => (λ_ (𝟙_ C)).inv ≫ (f ⊗ₘ repeatedUnitInput f n)

/-- 同じ対角入力は、単位の標準縮約と同じテンソル冪の射によって得られる。 -/
lemma repeatedUnitInput_eq (f : 𝟙_ C ⟶ X) (n : ℕ) :
    repeatedUnitInput f n =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso C n).inv ≫ SerrePositivity.TensorPowers.map f n := by
  induction n with
  | zero =>
    change 𝟙 (𝟙_ C) = 𝟙 (𝟙_ C) ≫ 𝟙 (𝟙_ C)
    simp
  | succ n ih =>
    simp only [repeatedUnitInput, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso, Iso.trans_inv,
      whiskerLeftIso_inv, SerrePositivity.TensorPowers.map, ih, Category.assoc,
      whiskerLeft_comp_tensorHom]

lemma repeatedUnitInput_index (f : 𝟙_ C ⟶ X) {m n : ℕ} (h : m = n) :
    repeatedUnitInput f m ≫ eqToHom (congrArg (power X) h) = repeatedUnitInput f n := by
  subst n
  simp

section Complex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {K : Complex A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] SerrePositivity.TensorPowers.power

/-- 単位係数による第二位置の代入を、同じ尾への作用として読む。 -/
lemma unitSecondInsertion (n : ℕ) (θ : power K n ⟶ K) :
    (λ_ (power K (1 + n))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K (𝟙_ (Complex A)) 1 n 1 ((λ_ (power K n)).hom ≫ θ) =
    eqToHom (congrArg (power K) (Nat.one_add n)) ≫ (K ◁ θ) ≫
      (K ◁ (oneIso K).inv) := by
  have ha : appendIso K n 0 = ρ_ (power K n) :=
    Iso.ext (appendIso_zero_right K n)
  change (λ_ (power K (1 + n))).inv ≫
    (𝟙_ (Complex A) ◁ (𝟙 (power K (1 + n)) ≫ (appendIso K 1 n).inv)) ≫
    (α_ (𝟙_ (Complex A)) (power K 1) (power K n)).inv ≫
    ((β_ (𝟙_ (Complex A)) (power K 1)).hom ▷ power K n) ≫
    (α_ (power K 1) (𝟙_ (Complex A)) (power K n)).hom ≫
    (power K 1 ◁ (𝟙_ (Complex A) ◁ (appendIso K n 0).inv)) ≫
    (power K 1 ◁ (α_ (𝟙_ (Complex A)) (power K n) (𝟙_ (Complex A))).inv) ≫
    (power K 1 ◁ (((λ_ (power K n)).hom ≫ θ) ▷ (𝟙_ (Complex A)))) ≫
    (appendIso K 1 1).hom ≫ 𝟙 (power K 2) = _
  rw [ha]
  simp only [appendIso, power, oneIso, Iso.trans_inv, Iso.trans_hom,
    whiskerLeftIso_inv, whiskerLeftIso_hom, eqToIso.inv, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.comp_id,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [braiding_tensorUnit_left]
  monoidal
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.id_comp, Category.comp_id, whiskerLeft_id,
    whiskerLeft_comp, comp_whiskerRight, whiskerLeft_eqToHom,
    eqToHom_trans_assoc]
  monoidal

/-- 同じ対角入力の第二位置への代入は、残り n 入力の値を第二因子へ入れること。 -/
lemma repeatedUnitInput_secondInsertion (f : 𝟙_ (Complex A) ⟶ K) (n : ℕ)
    (θ : power K n ⟶ K) :
    repeatedUnitInput f (1 + n) ≫ (λ_ (power K (1 + n))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K (𝟙_ (Complex A)) 1 n 1 ((λ_ (power K n)).hom ≫ θ) =
    (λ_ (𝟙_ (Complex A))).inv ≫ (f ⊗ₘ (repeatedUnitInput f n ≫ θ)) ≫
      (K ◁ (oneIso K).inv) := by
  rw [unitSecondInsertion, ← Category.assoc, repeatedUnitInput_index f (Nat.one_add n)]
  simp only [repeatedUnitInput, Category.assoc, tensorHom_comp_whiskerLeft_assoc]

end Complex
end SerrePositivity.EInfinity.PowerOperation
