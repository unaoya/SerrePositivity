module

public import SerrePositivity.KST.LocalizingInvariants.TensorTripleComposition
public import Mathlib.CategoryTheory.Monoidal.Bimod

/-!
概要：正則双加群への単射と、元の積の左右の閉性から、実双加群を構成する。
方針：単射で各作用則を消去し、元の代数の単位・結合則を三重 tensor に移す。
規約：可換性を要求しない。使われ方：Postnikov cycles 層の実 dg 双加群構造。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def bimoduleAlongMono (A : Mon C) {P : C} (i : P ⟶ A.X) [Mono i]
    (l : A.X ⊗ P ⟶ P) (r : P ⊗ A.X ⟶ P)
    (hl : l ≫ i = (A.X ◁ i) ≫ μ[A.X])
    (hr : r ≫ i = (i ▷ A.X) ≫ μ[A.X]) : Bimod A A where
  X := P
  actLeft := l
  actRight := r
  one_actLeft := by
    apply (cancel_mono i).1
    calc
      ((η[A.X] ▷ P) ≫ l) ≫ i = (η[A.X] ⊗ₘ i) ≫ μ[A.X] := by
        simp only [Category.assoc, hl, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (𝟙_ C ◁ i) ≫ (η[A.X] ▷ A.X) ≫ μ[A.X] := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (λ_ P).hom ≫ i := by rw [MonObj.one_mul, leftUnitor_naturality]
  actRight_one := by
    apply (cancel_mono i).1
    calc
      ((P ◁ η[A.X]) ≫ r) ≫ i = (i ⊗ₘ η[A.X]) ≫ μ[A.X] := by
        simp only [Category.assoc, hr, ← id_tensorHom, ← tensorHom_id,
          tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      _ = (i ▷ 𝟙_ C) ≫ (A.X ◁ η[A.X]) ≫ μ[A.X] := by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
          Category.id_comp, Category.comp_id]
      _ = (ρ_ P).hom ≫ i := by rw [MonObj.mul_one, rightUnitor_naturality]
  left_assoc := by
    apply (cancel_mono i).1
    have h := congrArg (fun f ↦ ((𝟙 A.X ⊗ₘ 𝟙 A.X) ⊗ₘ i) ≫ f) (MonObj.mul_assoc A.X)
    rw [tensorTriple_mul_left, tensorTriple_mul_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, hl, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h
  right_assoc := by
    apply (cancel_epi (α_ P A.X A.X).hom).1
    apply (cancel_mono i).1
    have h := congrArg (fun f ↦ ((i ⊗ₘ 𝟙 A.X) ⊗ₘ 𝟙 A.X) ≫ f) (MonObj.mul_assoc A.X)
    rw [tensorTriple_mul_left, tensorTriple_mul_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, hr, ← id_tensorHom,
      ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Category.comp_id] using h.symm
  middle_assoc := by
    apply (cancel_mono i).1
    have h := congrArg (fun f ↦ ((𝟙 A.X ⊗ₘ i) ⊗ₘ 𝟙 A.X) ≫ f) (MonObj.mul_assoc A.X)
    rw [tensorTriple_mul_left, tensorTriple_mul_right] at h
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp] at h
    simpa only [Category.assoc, hl, hr, ← id_tensorHom, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id] using h

end SerrePositivity.KST.LocalizingInvariants
