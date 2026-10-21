module
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 元の可逆な豊穣単位による Hom 族の合成判定
概要：元の単位が可逆なら、単位を保つ Hom 族は、その単位を含む合成を保つ。
方針：元の単位と tensor 恒等の可逆な射で前合成し、元の豊穣単位律へ帰着する。
規約：元の全 Hom・合成を保持。使われ方：標準単体の逆 dg 関手の対角合成。
-/
@[expose] public section
noncomputable section
universe u v w w'
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {C : Type w} {D : Type w'} [EnrichedCategory V C] [EnrichedCategory V D]

/-- 元の可逆な左単位を保つ二つの Hom 射は、元の左対角を含む合成を保つ。 -/
lemma enrichedHom_left_unit_composition (x z : C) (X Z : D) [IsIso (eId V x)]
    (f : (x ⟶[V] x) ⟶ (X ⟶[V] X)) (g : (x ⟶[V] z) ⟶ (X ⟶[V] Z))
    (hf : eId V x ≫ f = eId V X) :
    eComp V x x z ≫ g = (f ⊗ₘ g) ≫ eComp V X X Z := by
  let H := x ⟶[V] z
  let H' := X ⟶[V] Z
  let t : H ⟶ (x ⟶[V] x) ⊗ H := (λ_ H).inv ≫ eId V x ▷ H
  have : IsIso t := by dsimp [t]; infer_instance
  have hl : t ≫ eComp V x x z = 𝟙 H :=
    (Category.assoc _ _ _).trans (e_id_comp V x z)
  have hr : t ≫ (f ⊗ₘ g) ≫ eComp V X X Z = g := by
    dsimp only [t]
    rw [Category.assoc]
    rw [← tensorHom_id]
    rw [tensorHom_comp_tensorHom_assoc, hf, Category.id_comp]
    have hfac : eId V X ⊗ₘ g =
        (𝟙 (𝟙_ V) ⊗ₘ g) ≫ (eId V X ⊗ₘ 𝟙 H') := by
      rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    have hU : (λ_ H).inv ≫ (𝟙 (𝟙_ V) ⊗ₘ g) = g ≫ (λ_ H').inv := by
      simpa only [id_tensorHom] using (leftUnitor_inv_naturality g).symm
    have ht : (λ_ H').inv ≫ (eId V X ⊗ₘ 𝟙 H') ≫ eComp V X X Z = 𝟙 H' := by
      simpa only [tensorHom_id] using e_id_comp V X Z
    rw [hfac, Category.assoc (𝟙 (𝟙_ V) ⊗ₘ g) (eId V X ⊗ₘ 𝟙 H'),
      ← Category.assoc (λ_ H).inv (𝟙 (𝟙_ V) ⊗ₘ g), hU,
      Category.assoc g, ht, Category.comp_id]
  apply (cancel_epi t).1
  exact ((Category.assoc t _ _).symm.trans
    ((congrArg (fun f => f ≫ g) hl).trans (Category.id_comp _))).trans hr.symm

/-- 元の可逆な右単位を保つ二つの Hom 射は、元の右対角を含む合成を保つ。 -/
lemma enrichedHom_right_unit_composition (x z : C) (X Z : D) [IsIso (eId V z)]
    (f : (x ⟶[V] z) ⟶ (X ⟶[V] Z)) (g : (z ⟶[V] z) ⟶ (Z ⟶[V] Z))
    (hg : eId V z ≫ g = eId V Z) :
    eComp V x z z ≫ f = (f ⊗ₘ g) ≫ eComp V X Z Z := by
  let H := x ⟶[V] z
  let H' := X ⟶[V] Z
  let t : H ⟶ H ⊗ (z ⟶[V] z) := (ρ_ H).inv ≫ H ◁ eId V z
  have : IsIso t := by dsimp [t]; infer_instance
  have hl : t ≫ eComp V x z z = 𝟙 H :=
    (Category.assoc _ _ _).trans (e_comp_id V x z)
  have hr : t ≫ (f ⊗ₘ g) ≫ eComp V X Z Z = f := by
    dsimp only [t]
    rw [Category.assoc, ← id_tensorHom]
    rw [tensorHom_comp_tensorHom_assoc, hg, Category.id_comp]
    have hfac : f ⊗ₘ eId V Z =
        (f ⊗ₘ 𝟙 (𝟙_ V)) ≫ (𝟙 H' ⊗ₘ eId V Z) := by
      rw [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have hU : (ρ_ H).inv ≫ (f ⊗ₘ 𝟙 (𝟙_ V)) = f ≫ (ρ_ H').inv := by
      simpa only [tensorHom_id] using (rightUnitor_inv_naturality f).symm
    have ht : (ρ_ H').inv ≫ (𝟙 H' ⊗ₘ eId V Z) ≫ eComp V X Z Z = 𝟙 H' := by
      simpa only [id_tensorHom] using e_comp_id V X Z
    rw [hfac, Category.assoc (f ⊗ₘ 𝟙 (𝟙_ V)) (𝟙 H' ⊗ₘ eId V Z),
      ← Category.assoc (ρ_ H).inv (f ⊗ₘ 𝟙 (𝟙_ V)), hU,
      Category.assoc f, ht, Category.comp_id]
  apply (cancel_epi t).1
  exact ((Category.assoc t _ _).symm.trans
    ((congrArg (fun g => g ≫ f) hl).trans (Category.id_comp _))).trans hr.symm

end SerrePositivity.KST.SConstruction
