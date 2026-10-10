module

public import SerrePositivity.Asymptotic.FreeSequence
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# 自由列の係数変更

標準基底の行列の係数に環準同型を適用して、自由列の加法関手を作る。
ランク列は変わらないので `O(s)`・`o(s)` の条件を保つ。
環の自己同型によるひねりも同じ構成を使う。
一般の加群上のテンソル積との比較はこのファイルの主張には含めない。
-/

@[expose] public section

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory Filter Asymptotics

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] {s : ℕ → ℕ}

/-- 標準自由加群間の線形写像の行列に環準同型を施す。 -/
noncomputable def changeMatrix (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    (Fin a → S) →ₗ[S] (Fin b → S) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map φ)

/-- 行列の係数変更は恒等写像を保つ。 -/
@[simp] lemma changeMatrix_id (φ : R →+* S) (a : ℕ) :
    changeMatrix φ (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) = LinearMap.id := by
  simp [changeMatrix, LinearMap.toMatrix'_id, Matrix.map_one _ φ.map_zero φ.map_one]

/-- 行列の係数変更は合成を保つ。 -/
lemma changeMatrix_comp (φ : R →+* S) {a b c : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (g : (Fin b → R) →ₗ[R] (Fin c → R)) :
    changeMatrix φ (g.comp f) = (changeMatrix φ g).comp (changeMatrix φ f) := by
  simp [changeMatrix, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]

/-- 行列の係数変更は加法を保つ。 -/
lemma changeMatrix_add (φ : R →+* S) {a b : ℕ}
    (f g : (Fin a → R) →ₗ[R] (Fin b → R)) :
    changeMatrix φ (f + g) = changeMatrix φ f + changeMatrix φ g := by
  simp [changeMatrix, Matrix.map_add _ φ.map_add]

/-- 環準同型による自由加群列の係数変更関手。 -/
noncomputable def changeRing (φ : R →+* S) : FreeSequence R s ⥤ FreeSequence S s where
  obj X := ⟨X.rank, X.rank_isBigO⟩
  map f n := changeMatrix φ (f n)
  map_id X := funext fun n ↦ changeMatrix_id φ (X.rank n)
  map_comp f g := funext fun n ↦ changeMatrix_comp φ (f n) (g n)

instance (φ : R →+* S) : (changeRing (s := s) φ).Additive where
  map_add {X Y} f g := by
    apply hom_ext
    intro n
    change changeMatrix φ (f n + g n) = changeMatrix φ (f n) + changeMatrix φ (g n)
    exact changeMatrix_add φ (f n) (g n)

/-- 係数変更は各段の基底の個数を保つ。 -/
@[simp] lemma changeRing_rank (φ : R →+* S) (X : FreeSequence R s) :
    ((changeRing φ).obj X).rank = X.rank := rfl

/-- ランクが `o(s)` の自由列は、係数変更後も同じ条件を満たす。 -/
lemma changeRing_rank_isLittleO (φ : R →+* S) (X : FreeSequence R s)
    (hX : (fun n ↦ (X.rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ))) :
    (fun n ↦ (((changeRing φ).obj X).rank n : ℝ)) =o[atTop] (fun n ↦ (s n : ℝ)) := hX

end SerrePositivity.Asymptotic.FreeSequence
