module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition

/-!
概要：次数付き加群の写像を、IⁿM と M/IⁿM の実際の写像へ送る。
方針：拡大イデアルの冪の保存と、商への線形写像の降下を使う。
規約：基底環と多項式環を固定する。
使われ方：非 flat な閉厚化にも適用できる Čech 形式関数の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M N : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (I : Ideal R) (f : M →ₗ[MvPolynomial ι R] N)

local instance moduleMapSourceSubmodule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance moduleMapTargetSubmodule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := N) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := N) I n
local instance moduleMapSourceQuotient (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance moduleMapTargetQuotient (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n

/-- 多項式加群の写像を、実際の IⁿM の間の写像に制限する。 -/
def reesAdicProjectiveSubmoduleMap (n : ℕ) :
    reesAdicProjectiveSubmodule (ι := ι) (M := M) I n →ₗ[MvPolynomial ι R]
      reesAdicProjectiveSubmodule (ι := ι) (M := N) I n where
  toFun x := ⟨f x.val, reesExtendedAdic_map_mem (S := MvPolynomial ι R) I
    (f.restrictScalars R) n x.val x.property⟩
  map_add' x y := Subtype.ext (f.map_add x.val y.val)
  map_smul' r x := Subtype.ext (f.map_smul r x.val)

/-- 多項式加群の写像を、実際の I 進閉厚化の商の間へ降ろす。 -/
def reesAdicProjectiveQuotientMap (n : ℕ) :
    reesAdicProjectiveQuotient (ι := ι) (M := M) I n →ₗ[MvPolynomial ι R]
      reesAdicProjectiveQuotient (ι := ι) (M := N) I n :=
  (((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
    (⊤ : Submodule (MvPolynomial ι R) M))).mapQ
    (((I.map (algebraMap R (MvPolynomial ι R))) ^ n •
      (⊤ : Submodule (MvPolynomial ι R) N))) f
    (fun x hx ↦ reesExtendedAdic_map_mem (S := MvPolynomial ι R) I
      (f.restrictScalars R) n x hx)

/-- IⁿM の包含と加群写像の四角形は可換。 -/
theorem reesAdicProjectiveSubmoduleMap_inclusion (n : ℕ) :
    (reesAdicProjectiveToModule (ι := ι) (M := N) I n).comp
      (reesAdicProjectiveSubmoduleMap I f n) =
    f.comp (reesAdicProjectiveToModule (ι := ι) (M := M) I n) := rfl

/-- 閉厚化への射影と加群写像の四角形は可換。 -/
theorem reesAdicProjectiveQuotientMap_projection (n : ℕ) :
    (reesAdicProjectiveQuotientMap I f n).comp
      (reesAdicProjectiveQuotientProjection (ι := ι) (M := M) I n) =
    (reesAdicProjectiveQuotientProjection (ι := ι) (M := N) I n).comp f := by
  apply LinearMap.ext
  intro m
  rfl

/-- 加群写像からの商写像は、閉厚化の遷移と可換。 -/
theorem reesAdicProjectiveQuotientMap_transition (i j : ℕ) (h : j ≤ i) :
    (reesAdicProjectiveQuotientTransition (ι := ι) (M := N) I i j h).comp
      (reesAdicProjectiveQuotientMap I f i) =
    (reesAdicProjectiveQuotientMap I f j).comp
      (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h) := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I i x
  rfl

variable (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable (hf : ∀ j, ∀ x ∈ G j, f x ∈ H j)
include hf

/-- IⁿM の間の写像は、元の写像が保つ Proj 次数を保つ。 -/
theorem reesAdicProjectiveSubmoduleMap_preservesPiece (n j : ℕ)
    (x : reesAdicProjectiveSubmodule (ι := ι) (M := M) I n)
    (hx : x ∈ reesAdicProjectivePiece (ι := ι) I G n j) :
    reesAdicProjectiveSubmoduleMap I f n x ∈ reesAdicProjectivePiece (ι := ι) I H n j :=
  hf j x.val hx

/-- 閉厚化の商写像は、元の写像が保つ Proj 次数を保つ。 -/
theorem reesAdicProjectiveQuotientMap_preservesPiece (n j : ℕ)
    (x : reesAdicProjectiveQuotient (ι := ι) (M := M) I n)
    (hx : x ∈ reesAdicProjectiveQuotientPiece (ι := ι) I G n j) :
    reesAdicProjectiveQuotientMap I f n x ∈
      reesAdicProjectiveQuotientPiece (ι := ι) I H n j := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact ⟨f m, hf j m hm, rfl⟩

end SerrePositivity.AlgebraicGeometry
