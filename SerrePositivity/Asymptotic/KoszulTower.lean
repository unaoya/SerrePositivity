module

public import SerrePositivity.Asymptotic.SequenceKoszulSupport
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 複体列の Koszul 構成を共通の反復錐定理へ渡す

支持と零作用は三角関手の像でのみ要求する。したがってランク商で零となる
スカラーを扱う際、元の複体列に一様支持を加える必要がない。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}
  {D : Type*} [Category* D] [Preadditive D] [Linear R D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] [Pretriangulated D]
  (F : SequenceHomotopy R s ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  {e : ℕ} (z : Fin e → R) (x : ℕ → R)
  (K : CochainComplex (FreeSequence R s) ℤ) (hK : strictlyBoundedComplex _ K)
  (h : scalarSupported z (F.obj (sequenceHomotopyObj K hK)))

/-- 各段を、関手の像における支持部分圏の対象とする。 -/
noncomputable def sequenceKoszulTowerObj (k : ℕ) : (scalarSupported (C := D) z).FullSubcategory :=
  ⟨F.obj (sequenceHomotopyObj (sequenceKoszul (fun j : Fin k ↦ x j) K)
    (sequenceKoszul_bounded _ K hK)), sequenceKoszul_map_supported F z _ K hK h⟩

/-- 実際の Koszul の写像錐を三角関手で送り、支持部分圏へ制限する。 -/
@[implicit_reducible]
noncomputable def sequenceKoszulTowerTriangle (k : ℕ) :
    Triangle (scalarSupported (C := D) z).FullSubcategory :=
  let P := sequenceKoszul (fun j : Fin k ↦ x j) K
  let hP := sequenceKoszul_bounded (fun j : Fin k ↦ x j) K hK
  fullSubcategoryTriangle (scalarSupported (C := D) z)
    (F.mapTriangle.obj (sequenceConeTriangle (x k • 𝟙 P) hP hP))
    (sequenceKoszulTowerObj F z x K hK h k).property
    (sequenceKoszulTowerObj F z x K hK h k).property
    (sequenceKoszulTowerObj F z x K hK h (k + 1)).property

omit [F.Linear R] in
lemma sequenceKoszulTowerTriangle_distinguished (k : ℕ) :
    sequenceKoszulTowerTriangle F z x K hK h k ∈ distTriang _ :=
  fullSubcategoryTriangle_distinguished _ _ _ _ _
    (F.map_distinguished _ (sequenceConeTriangle_distinguished _ _ _))

@[simp] lemma sequenceKoszulTowerTriangle_mor₁ (k : ℕ) :
    (sequenceKoszulTowerTriangle F z x K hK h k).mor₁ =
      x k • 𝟙 (sequenceKoszulTowerObj F z x K hK h k) := by
  apply ObjectProperty.hom_ext
  let P := sequenceKoszul (fun j : Fin k ↦ x j) K
  let hP := sequenceKoszul_bounded (fun j : Fin k ↦ x j) K hK
  change F.map (show sequenceHomotopyObj P hP ⟶ sequenceHomotopyObj P hP from
    (sequenceConeTriangle (x k • 𝟙 P) hP hP).mor₁) = _
  rw [sequenceConeTriangle_smul_mor₁, F.map_smul, F.map_id]
  rfl

lemma sequenceKoszulTowerTriangle_mk_distinguished (k : ℕ) :
    Triangle.mk (x k • 𝟙 (sequenceKoszulTowerObj F z x K hK h k))
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₂
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₃ ∈ distTriang _ := by
  rw [← sequenceKoszulTowerTriangle_mor₁ F z x K hK h k]
  exact sequenceKoszulTowerTriangle_distinguished F z x K hK h k

/-- 商での零作用を使い、具体的な Koszul 列を零射の錐の列にする。 -/
lemma sequenceKoszulTower_zero_triangles (n : ℕ)
    (hx : ∀ j < n, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0) :
    ∀ k < n, Triangle.mk (0 : sequenceKoszulTowerObj F z x K hK h k ⟶ _)
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₂
      (sequenceKoszulTowerTriangle F z x K hK h k).mor₃ ∈ distTriang _ :=
  iteratedScalarCone_zero_triangles (sequenceKoszulTowerObj F z x K hK h)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₂)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₃) n x
    (fun k _ ↦ sequenceKoszulTowerTriangle_mk_distinguished F z x K hK h k)
    (fun j hj ↦ ObjectProperty.hom_ext _ (hx j hj))

variable {A : Type*} [Category* A] [Abelian A]
  (H : (scalarSupported (C := D) z).FullSubcategory ⥤ A)
  [H.IsHomological] [H.ShiftSequence ℤ]

/-- 実際の複体列の消滅は共通の対象としての消滅定理の適用。
元の列への一様支持も、長さの忠実性も仮定しない。 -/
theorem sequenceKoszulTower_vanishing (n : ℕ)
    (hx : ∀ j < n, x j • 𝟙 (F.obj (sequenceHomotopyObj K hK)) = 0)
    (a b : ℤ)
    (hKos : ∀ q, q < a ∨ b < q →
      IsZero ((H.shift q).obj (sequenceKoszulTowerObj F z x K hK h n)))
    (q : ℤ) (hq : q < a + n ∨ b < q) :
    IsZero ((H.shift q).obj (sequenceKoszulTowerObj F z x K hK h 0)) :=
  iteratedZeroCone_vanishing (sequenceKoszulTowerObj F z x K hK h)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₂)
    (fun k ↦ (sequenceKoszulTowerTriangle F z x K hK h k).mor₃) n
    (sequenceKoszulTower_zero_triangles F z x K hK h n hx) H a b hKos q hq

end SerrePositivity.Asymptotic
