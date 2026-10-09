module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.TriangleSmul
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# 台の条件をホモトピー圏で扱う

台の条件 `IsSupported z P`（`z_j^v • 𝟙 P` が零ホモトピック）を、ホモトピー圏 `K(A)` での等式
`z_j^v • 𝟙 = 0` に言い換え、ホモトピー同値・シフト・写像錐で保たれることを示す。
Koszul 複体 `K(x)` は `x` に台をもつ。一般的な部分は `HomologicalAlgebra/TriangleSmul.lean`。
台をもつ複体のホモロジーは `z` の冪で消える（`IsSupported.le_radical_annihilator`）。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 台の条件のホモトピー圏での言い換え。 -/
lemma isSupported_iff {e : ℕ} (z : Fin e → R) (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsSupported z P ↔ ∃ v : ℕ, ∀ j, (z j) ^ v • 𝟙 ((homotopyQuot R).obj P) = 0 := by
  simp only [IsSupported, nonempty_homotopy_smul_id_zero_iff]

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

/-! ## ホモロジーの零化 -/

/-- 零ホモトピックな `z_j^v • 𝟙` はホモロジーを零化する：`(z) ≤ √(Ann H^i(P))`。 -/
lemma IsSupported.le_radical_annihilator {e : ℕ} {w : Fin e → R}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsSupported w P) (i : ℤ) :
    Ideal.span (Set.range w) ≤ (Module.annihilator R (P.homology i)).radical := by
  obtain ⟨v, hv⟩ := hP
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  refine ⟨v, ?_⟩
  obtain ⟨H⟩ := hv j
  have h := H.homologyMap_eq i
  rw [homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  rw [Module.mem_annihilator]
  intro x
  exact congrArg (fun f : P.homology i ⟶ P.homology i ↦ f.hom x) h

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

/-! ## 基底変更とひねり -/

section baseChange

variable {A C : Type u} [CommRing A] [CommRing C]

/-- 台は基底変更で保たれる。 -/
lemma isSupported_baseChange (φ : A →+* C) {e : ℕ} {z : Fin e → A}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (h : IsSupported z P) :
    IsSupported (φ ∘ z) (baseChange φ P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have := (ModuleCat.extendScalars.{u, u, u} φ).mapHomotopy H
  rw [extendScalars_mapHomologicalComplex_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero, map_pow] at this
  exact ⟨this⟩

end baseChange

section twist

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] {G : Type u} [Group G]
  [MulSemiringAction G T] [SMulCommClass G A T]

/-- 係数制限は `f` で固定される元によるスカラー倍と両立する。 -/
lemma restrictScalars_mapHomologicalComplex_smul_of_fixed (f : T →+* T) (c : T) (hc : f c = c)
    {ι : Type*} {cs : ComplexShape ι} {K L : HomologicalComplex (ModuleCat.{u} T) cs} (u : K ⟶ L) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map (c • u) =
      c • ((ModuleCat.restrictScalars f).mapHomologicalComplex _).map u := by
  ext i x
  change c • (u.f i x) = f c • (u.f i x)
  rw [hc]

/-- `A` 上の作用は `A` の元の像を固定する。 -/
lemma toRingHom_algebraMap (g : G) (a : A) :
    MulSemiringAction.toRingHom G T g (algebraMap A T a) = algebraMap A T a := by
  change g • algebraMap A T a = algebraMap A T a
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

/-- `A` から来る台はひねりで保たれる。 -/
lemma isSupported_twist {e : ℕ} (z : Fin e → A) (g : G) {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : IsSupported (algebraMap A T ∘ z) P) : IsSupported (algebraMap A T ∘ z) (twist g P) := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v, fun j ↦ ?_⟩
  obtain ⟨H⟩ := hv j
  have hfix : MulSemiringAction.toRingHom G T g ((algebraMap A T ∘ z) j ^ v) =
      (algebraMap A T ∘ z) j ^ v := by
    rw [map_pow, Function.comp_apply, toRingHom_algebraMap]
  have := (ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomotopy H
  rw [restrictScalars_mapHomologicalComplex_smul_of_fixed _ _ hfix, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at this
  exact ⟨this⟩

end twist

end SerrePositivity
