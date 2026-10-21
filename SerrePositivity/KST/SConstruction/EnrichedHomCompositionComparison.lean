module
public import Mathlib.CategoryTheory.Enriched.Basic

/-! # 元の可逆な tensor 比較による豊穣合成保存の判定
概要：元の Hom 比較と tensor 比較への制限で、元の豊穣合成保存を判定する。
方針：元の可逆な比較射を前合成して消去し、tensor 合成則を使う。
規約：元の全 Hom と実射を保持。使われ方：標準区間比較からの逆 dg 関手の合成保存。
-/
@[expose] public section
universe u v w w'
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]
  {C : Type w} {D : Type w'} [EnrichedCategory V C] [EnrichedCategory V D]

/-- 元の可逆な Hom・tensor 比較への制限が合成を保てば、元の Hom 族も合成を保つ。 -/
lemma enrichedHom_composition_of_tensor_comparison (x y z : C) (X Y Z : D)
    {P Q R : V} (e : P ≅ (x ⟶[V] y)) (f : Q ≅ (y ⟶[V] z)) (t : R ≅ P ⊗ Q)
    (α : (x ⟶[V] y) ⟶ (X ⟶[V] Y)) (β : (y ⟶[V] z) ⟶ (Y ⟶[V] Z))
    (γ : (x ⟶[V] z) ⟶ (X ⟶[V] Z))
    (h : (t.hom ≫ (e.hom ⊗ₘ f.hom) ≫ eComp V x y z) ≫ γ =
      t.hom ≫ ((e.hom ≫ α) ⊗ₘ (f.hom ≫ β)) ≫ eComp V X Y Z) :
    eComp V x y z ≫ γ = (α ⊗ₘ β) ≫ eComp V X Y Z := by
  apply (cancel_epi (e.hom ⊗ₘ f.hom)).mp
  apply (cancel_epi t.hom).mp
  simpa only [← tensorHom_comp_tensorHom, Category.assoc] using h

end SerrePositivity.KST.SConstruction
