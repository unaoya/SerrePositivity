module

public import SerrePositivity.PerfectComplex.HomotopyCategory
public import SerrePositivity.CategoryTheory.HomotopyProperty
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 有限射影複体の実際の Koszul 錐の列

任意の可換環上で、係数つき Koszul 複体を支持部分圏の完全三角形の列として
構成する。消滅の結論は共通の反復錐定理へ渡す。長さ・平坦性はここでは使わない。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R]

lemma strictlyPerfectComplex_koszulComplexOn {n : ℕ} (x : Fin n → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P) :
    strictlyPerfectComplex R (koszulComplexOn x P) := by
  induction n with
  | zero => exact hP
  | succ n ih => exact strictlyPerfectComplex_mappingCone R _ (ih _) (ih _)

lemma IsSupported.koszulComplexOn {e n : ℕ} {z : Fin e → R}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : IsSupported z P) (x : Fin n → R) :
    IsSupported z (koszulComplexOn x P) := by
  induction n with
  | zero => exact hP
  | succ n ih => exact (ih _).mappingCone _ (ih _)

/-- 有限射影複体の射の実際の写像錐三角形。 -/
@[implicit_reducible]
noncomputable def perfectConeTriangle {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : strictlyPerfectComplex R P) (hQ : strictlyPerfectComplex R Q) :
    Triangle (PerfectHomotopy R) :=
  fullSubcategoryTriangle (perfectHomotopyProperty R) (CochainComplex.mappingCone.triangleh f)
    ((perfectHomotopyProperty_quotient R P).mpr hP)
    ((perfectHomotopyProperty_quotient R Q).mpr hQ)
    ((perfectHomotopyProperty_quotient R _).mpr
      (strictlyPerfectComplex_mappingCone R f hP hQ))

lemma perfectConeTriangle_distinguished {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : strictlyPerfectComplex R P) (hQ : strictlyPerfectComplex R Q) :
    perfectConeTriangle f hP hQ ∈ distTriang _ :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (HomotopyCategory.mappingCone_triangleh_distinguished f)

variable {e : ℕ} (z : Fin e → R) (x : ℕ → R)
  (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
  (hs : IsSupported z P)

/-- 最初の `k` 個のスカラーによる Koszul 複体を、支持部分圏の対象とする。 -/
noncomputable def perfectKoszulObj (k : ℕ) : SupportedPerfectHomotopy z :=
  ⟨perfectHomotopyObj R (koszulComplexOn (fun j : Fin k ↦ x j) P)
    (strictlyPerfectComplex_koszulComplexOn _ P hP),
    (perfectHomotopyObj_supported_iff z _ _).mpr (hs.koszulComplexOn _)⟩

/-- Koszul の一段を支持つき有限射影圏の完全三角形として実現する。 -/
@[implicit_reducible]
noncomputable def perfectKoszulTriangle (k : ℕ) : Triangle (SupportedPerfectHomotopy z) :=
  let Q := koszulComplexOn (fun j : Fin k ↦ x j) P
  let hQ := strictlyPerfectComplex_koszulComplexOn (fun j : Fin k ↦ x j) P hP
  fullSubcategoryTriangle (scalarSupported (C := PerfectHomotopy R) z)
    (perfectConeTriangle (smulId (x k) Q) hQ hQ)
    (perfectKoszulObj z x P hP hs k).property (perfectKoszulObj z x P hP hs k).property
    (perfectKoszulObj z x P hP hs (k + 1)).property

lemma perfectKoszulTriangle_distinguished (k : ℕ) :
    perfectKoszulTriangle z x P hP hs k ∈ distTriang _ :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _ (perfectConeTriangle_distinguished _ _ _)

@[simp] lemma perfectKoszulTriangle_mor₁ (k : ℕ) :
    (perfectKoszulTriangle z x P hP hs k).mor₁ =
      x k • 𝟙 (perfectKoszulObj z x P hP hs k) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  let Q := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  change Q.map (x k • 𝟙 (koszulComplexOn (fun j : Fin k ↦ x j) P)) =
    x k • 𝟙 (Q.obj (koszulComplexOn (fun j : Fin k ↦ x j) P))
  exact (Q.map_smul (x k) _).trans (congrArg (fun f ↦ x k • f) (Q.map_id _))

/-- 具体的な Koszul 列を抽象的なスカラー錐の列として使うための証明。 -/
lemma perfectKoszulTriangle_mk_distinguished (k : ℕ) :
    Triangle.mk (x k • 𝟙 (perfectKoszulObj z x P hP hs k))
      (perfectKoszulTriangle z x P hP hs k).mor₂
      (perfectKoszulTriangle z x P hP hs k).mor₃ ∈ distTriang _ := by
  rw [← perfectKoszulTriangle_mor₁ z x P hP hs k]
  exact perfectKoszulTriangle_distinguished z x P hP hs k

/-- 初項で零ホモトピックなスカラーは、支持圏で零射の錐の列を与える。 -/
lemma perfectKoszul_zero_triangles (n : ℕ)
    (hx : ∀ j < n, Nonempty (Homotopy (smulId (x j) P) 0)) :
    ∀ k < n, Triangle.mk (0 : perfectKoszulObj z x P hP hs k ⟶ _)
      (perfectKoszulTriangle z x P hP hs k).mor₂
      (perfectKoszulTriangle z x P hP hs k).mor₃ ∈ distTriang _ := by
  apply iteratedScalarCone_zero_triangles (perfectKoszulObj z x P hP hs)
    (fun k ↦ (perfectKoszulTriangle z x P hP hs k).mor₂)
    (fun k ↦ (perfectKoszulTriangle z x P hP hs k).mor₃) n x
    (fun k _ ↦ perfectKoszulTriangle_mk_distinguished z x P hP hs k)
  intro j hj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact (nonempty_homotopy_smul_id_zero_iff (x j) P).mp (hx j hj)

variable {A : Type*} [Category* A] [Abelian A]
  (F : SupportedPerfectHomotopy z ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ]

/-- 有限射影版の消滅は、実際の Koszul 列に対する共通定理の適用である。 -/
theorem perfectKoszul_homological_vanishing (n : ℕ)
    (hx : ∀ j < n, Nonempty (Homotopy (smulId (x j) P) 0)) (m : ℤ)
    (h : ∀ i, i < 0 ∨ m < i →
      IsZero ((F.shift (-i)).obj (perfectKoszulObj z x P hP hs n)))
    (i : ℤ) (hi : i < 0 ∨ m - n < i) :
    IsZero ((F.shift (-i)).obj (perfectKoszulObj z x P hP hs 0)) := by
  apply iteratedScalarCone_homological_vanishing (perfectKoszulObj z x P hP hs)
    (fun k ↦ (perfectKoszulTriangle z x P hP hs k).mor₂)
    (fun k ↦ (perfectKoszulTriangle z x P hP hs k).mor₃) n F x
    (fun k _ ↦ perfectKoszulTriangle_mk_distinguished z x P hP hs k) ?_ m h i hi
  intro j hj
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact (nonempty_homotopy_smul_id_zero_iff (x j) P).mp (hx j hj)

end SerrePositivity
