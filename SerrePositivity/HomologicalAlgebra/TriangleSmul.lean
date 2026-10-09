module

public import SerrePositivity.HomologicalAlgebra.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# スカラー倍がホモトピー圏で消えること

- 三角形の補題：完全三角形 `X → Y → Z → X[1]` で `(a • 𝟙 Y) ≫ g = 0` かつ
  `h ≫ (a • 𝟙 X)⟦1⟧' = 0` なら `(a * a) • 𝟙 Z = 0`。
- `a • 𝟙 P` が零ホモトピックであることは、ホモトピー圏で `a • 𝟙 = 0` であることと同じ。
- 写像錐：`a` が `X`、`Y` 上で零ホモトピックなら `a²` は `Cone(f)` 上で零ホモトピック。
  `Cone(c • 𝟙 X)` には `c²` が零ホモトピックに作用する。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

/-! ## 完全三角形の補題 -/

section triangle

variable {R : Type*} [Ring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
  [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [(shiftFunctor C (1 : ℤ)).Linear R]

/-- 完全三角形 `X → Y → Z → X[1]` で `a` が `g` の前と `h` の後ろで消えるなら、`a²` は `Z` 上で `0`。 -/
lemma smul_mul_self_id_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) (a : R)
    (h₂ : (a • 𝟙 T.obj₂) ≫ T.mor₂ = 0)
    (h₃ : T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (a • 𝟙 T.obj₁) = 0) :
    (a * a) • 𝟙 T.obj₃ = 0 := by
  set u : T.obj₃ ⟶ T.obj₃ := a • 𝟙 T.obj₃
  have hu₂ : T.mor₂ ≫ u = 0 := by
    rw [Linear.comp_smul, Category.comp_id, ← h₂, Linear.smul_comp, Category.id_comp]
  have hu₃ : u ≫ T.mor₃ = 0 := by
    rw [← h₃, Linear.smul_comp, Category.id_comp, Functor.map_smul, CategoryTheory.Functor.map_id,
      Linear.comp_smul, Category.comp_id]
  obtain ⟨v, hv⟩ := Triangle.yoneda_exact₃ T hT u hu₂
  have : (a * a) • 𝟙 T.obj₃ = u ≫ u := by
    rw [mul_smul, Linear.smul_comp, Category.id_comp]
  rw [this]
  calc u ≫ u = u ≫ (T.mor₃ ≫ v) := by rw [← hv]
    _ = 0 := by rw [← Category.assoc, hu₃, zero_comp]

end triangle

variable {R : Type u} [CommRing R]

/-- ホモトピー圏 `K(R)` への商関手。 -/
noncomputable abbrev homotopyQuot (R : Type u) [CommRing R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _

/-- `a • 𝟙 P` が零ホモトピックであることは、ホモトピー圏で `a • 𝟙 = 0` であることと同じ。 -/
lemma nonempty_homotopy_smul_id_zero_iff (a : R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    Nonempty (Homotopy (a • 𝟙 P) 0) ↔ a • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff, Functor.map_smul, CategoryTheory.Functor.map_id]

/-- `a^v • 𝟙 = 0` なら `w ≥ v` で `a^w • 𝟙 = 0`。 -/
lemma pow_smul_id_eq_zero_of_le {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
    {a : R} {v w : ℕ} (h : a ^ v • 𝟙 X = 0) (hvw : v ≤ w) : a ^ w • 𝟙 X = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvw
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

section cone

variable {X Y : CochainComplex (ModuleCat.{u} R) ℤ}

/-- `a` が `X`、`Y` 上で零ホモトピックなら、`a²` は `Cone(f)` 上で零ホモトピック。 -/
lemma mappingCone_smul_mul_self_eq_zero (f : X ⟶ Y) (a : R)
    (hX : a • 𝟙 ((homotopyQuot R).obj X) = 0) (hY : a • 𝟙 ((homotopyQuot R).obj Y) = 0) :
    (a * a) • 𝟙 ((homotopyQuot R).obj (CochainComplex.mappingCone f)) = 0 :=
  smul_mul_self_id_eq_zero _ (HomotopyCategory.mappingCone_triangleh_distinguished f) a
    (by
      have h : a • 𝟙 (CochainComplex.mappingCone.triangleh f).obj₂ = 0 := hY
      rw [h, zero_comp])
    (by
      have h : a • 𝟙 (CochainComplex.mappingCone.triangleh f).obj₁ = 0 := hX
      rw [h, Functor.map_zero, comp_zero])

/-- `Cone(c • 𝟙 X)` には `c²` が零ホモトピックに作用する。 -/
lemma mappingCone_smulId_mul_self_eq_zero (c : R) :
    (c * c) • 𝟙 ((homotopyQuot R).obj (CochainComplex.mappingCone (smulId c X))) = 0 := by
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished (smulId c X)
  set T := CochainComplex.mappingCone.triangleh (smulId c X)
  have h₂ : c • 𝟙 T.obj₂ = T.mor₁ := by
    change c • 𝟙 ((homotopyQuot R).obj X) = (homotopyQuot R).map (c • 𝟙 X)
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have h₁ : c • 𝟙 T.obj₁ = T.mor₁ := h₂
  refine smul_mul_self_id_eq_zero T hT c ?_ ?_
  · rw [h₂]
    exact comp_distTriang_mor_zero₁₂ _ hT
  · rw [h₁]
    exact comp_distTriang_mor_zero₃₁ _ hT

end cone

end SerrePositivity
