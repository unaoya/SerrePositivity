module

public import SerrePositivity.Koszul
public import SerrePositivity.Perfect
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# 台の条件をホモトピー圏で扱う（Lemma 3.5b の準備、段階 1）

台の条件 `IsSupported z P`（`z_j^v • 𝟙 P` が零ホモトピック）を、ホモトピー圏 `K(A)` での等式
`z_j^v • 𝟙 = 0` に言い換え、次を示す。

- ホモトピー同値・シフトで保たれる。
- 三角形の補題：完全三角形 `X → Y → Z → X[1]` で `(a • 𝟙 Y) ≫ g = 0` かつ
  `h ≫ (a • 𝟙 X)⟦1⟧' = 0` なら `(a * a) • 𝟙 Z = 0`。
- 写像錐：`X`、`Y` が台をもてば `Cone(f)` も台をもつ。`Cone(c • 𝟙 X)` には `c²` が零ホモトピックに
  作用する。
- Koszul 複体 `K(x)` は `x` に台をもつ。
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

/-- 台の条件のホモトピー圏での言い換え。 -/
lemma isSupported_iff {e : ℕ} (z : Fin e → R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsSupported z P ↔ ∃ v : ℕ, ∀ j, (z j) ^ v • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  simp only [IsSupported, nonempty_homotopy_smul_id_zero_iff]

/-- `a^v • 𝟙 = 0` なら `w ≥ v` で `a^w • 𝟙 = 0`。 -/
lemma pow_smul_id_eq_zero_of_le {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
    {a : R} {v w : ℕ} (h : a ^ v • 𝟙 X = 0) (hvw : v ≤ w) : a ^ w • 𝟙 X = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hvw
  rw [pow_add, mul_comm, mul_smul, h, smul_zero]

/-- 各 `j` ごとに冪がとれれば、共通の冪がとれる。 -/
lemma isSupported_of_forall {e : ℕ} {z : Fin e → R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (h : ∀ j, ∃ v : ℕ, (z j) ^ v • 𝟙 ((homotopyQuot R).obj P) = 0) : IsSupported z P := by
  choose v hv using h
  rw [isSupported_iff]
  exact ⟨Finset.univ.sup v, fun j ↦
    pow_smul_id_eq_zero_of_le (hv j) (Finset.le_sup (Finset.mem_univ j))⟩

/-- ホモトピー圏での同型で台の条件は保たれる。 -/
lemma IsSupported.of_quotIso {e : ℕ} {z : Fin e → R} {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (i : (homotopyQuot R).obj P ≅ (homotopyQuot R).obj Q) (hP : IsSupported z P) :
    IsSupported z Q := by
  rw [isSupported_iff] at hP ⊢
  obtain ⟨v, hv⟩ := hP
  refine ⟨v, fun j ↦ ?_⟩
  have : (z j) ^ v • 𝟙 ((homotopyQuot R).obj Q) = i.inv ≫ ((z j) ^ v • 𝟙 _) ≫ i.hom := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.inv_hom_id]
  rw [this, hv j, zero_comp, comp_zero]

/-- ホモトピー同値で台の条件は保たれる。 -/
lemma IsSupported.of_homotopyEquiv {e : ℕ} {z : Fin e → R}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (h : HomotopyEquiv P Q) (hP : IsSupported z P) :
    IsSupported z Q :=
  hP.of_quotIso (HomotopyCategory.isoOfHomotopyEquiv h)

/-- シフトで台の条件は保たれる。 -/
lemma IsSupported.shift {e : ℕ} {z : Fin e → R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsSupported z P) (n : ℤ) : IsSupported z (P⟦n⟧) := by
  rw [isSupported_iff] at hP ⊢
  obtain ⟨v, hv⟩ := hP
  refine ⟨v, fun j ↦ ?_⟩
  let i := ((homotopyQuot R).commShiftIso n).app P
  have : (z j) ^ v • 𝟙 ((homotopyQuot R).obj (P⟦n⟧)) =
      i.hom ≫ (shiftFunctor _ n).map ((z j) ^ v • 𝟙 ((homotopyQuot R).obj P)) ≫ i.inv := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    simp
  rw [this, hv j, Functor.map_zero, zero_comp, comp_zero]

/-! ## 写像錐 -/

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

/-- `X`、`Y` が `z` に台をもてば `Cone(f)` も台をもつ。 -/
lemma IsSupported.mappingCone {e : ℕ} {z : Fin e → R} (f : X ⟶ Y) (hX : IsSupported z X)
    (hY : IsSupported z Y) : IsSupported z (CochainComplex.mappingCone f) := by
  rw [isSupported_iff] at hX hY
  obtain ⟨v, hv⟩ := hX
  obtain ⟨w, hw⟩ := hY
  refine isSupported_of_forall fun j ↦ ⟨(v ⊔ w) + (v ⊔ w), ?_⟩
  rw [pow_add]
  exact mappingCone_smul_mul_self_eq_zero f _ (pow_smul_id_eq_zero_of_le (hv j) le_sup_left)
    (pow_smul_id_eq_zero_of_le (hw j) le_sup_right)

end cone

/-! ## Koszul 複体の台 -/

/-- Koszul 複体 `K(x)` は `x` に台をもつ。 -/
theorem isSupported_koszulComplex : ∀ {n : ℕ} (x : Fin n → R), IsSupported x (koszulComplex x)
  | 0, x => ⟨0, fun j ↦ j.elim0⟩
  | n + 1, x => by
    have ih := isSupported_koszulComplex (Fin.init x)
    rw [isSupported_iff] at ih
    obtain ⟨v, hv⟩ := ih
    refine isSupported_of_forall fun j ↦ ?_
    change ∃ w : ℕ, (x j) ^ w • 𝟙 ((homotopyQuot R).obj
      (CochainComplex.mappingCone (smulId (x (Fin.last n)) (koszulComplex (Fin.init x))))) = 0
    induction j using Fin.lastCases with
    | last =>
      exact ⟨2, by rw [pow_two]; exact mappingCone_smulId_mul_self_eq_zero _⟩
    | cast j =>
      refine ⟨v + v, ?_⟩
      rw [pow_add]
      exact mappingCone_smul_mul_self_eq_zero _ _ (hv j) (hv j)

end SerrePositivity
