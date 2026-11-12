module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition

/-!
概要：実際の閉厚化の商の遷移の恒等・合成則を示す。
方針：商への射影の全射性を使い、元の加群の代表で確かめる。
規約：第 i 段から第 j 段への遷移には j≤i を使う。
使われ方：閉厚化の Čech コホモロジーを逆系として組み立てる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R M : Type u} {ι : Type} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R)
local instance quotientLawsModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n

/-- 閉厚化の同じ段の間の遷移は恒等写像。 -/
theorem reesAdicProjectiveQuotientTransition_self (n : ℕ) :
    reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I n n le_rfl = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I n x
  rfl

/-- 閉厚化の二つの遷移の合成は、直接の遷移に等しい。 -/
theorem reesAdicProjectiveQuotientTransition_comp
    (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) :
    (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I j k hjk).comp
      (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j hij) =
    reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i k (hjk.trans hij) := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := reesAdicProjectiveQuotientProjection_surjective (ι := ι) (M := M) I i x
  rfl

end SerrePositivity.AlgebraicGeometry
