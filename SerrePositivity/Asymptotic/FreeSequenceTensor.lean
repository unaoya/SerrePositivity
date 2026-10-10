module

public import SerrePositivity.Asymptotic.FreeSequenceBaseChange
public import SerrePositivity.Asymptotic.SequenceComplex
public import SerrePositivity.PerfectComplex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# 行列による自由列の係数変更とテンソル積の比較

標準自由加群のテンソル積の同型を、行列の射について自然な同型にまとめる。
各段の複体についても同型を得るので、有限版の Euler 評価の公式を適用できる。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic.FreeSequence

open CategoryTheory
open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}

/-- 行列への係数変更は、ベクトルの各係数への環準同型と両立する。 -/
lemma changeMatrix_apply_map (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : Fin a → R) :
    changeMatrix φ f (φ ∘ x) = φ ∘ f x := by
  funext j
  simp only [changeMatrix, Matrix.toLin'_apply, ← RingHom.map_mulVec,
    LinearMap.toMatrix'_mulVec, Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
/-- 標準自由加群の係数変更をテンソル積として実現する同型。 -/
noncomputable def standardTensorIso (φ : R →+* S) (a : ℕ) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (Fin a → R)) ≅
      ModuleCat.of S (Fin a → S) := by
  letI := φ.toAlgebra
  exact (TensorProduct.piScalarRight R S S (Fin a)).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- 標準自由加群のテンソル同型の自然性。 -/
lemma standardTensorIso_naturality (φ : R →+* S) {a b : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom f) ≫ (standardTensorIso φ b).hom =
      (standardTensorIso φ a).hom ≫ ModuleCat.ofHom (changeMatrix φ f) := by
  let := φ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  change (TensorProduct.piScalarRight R S S (Fin b)) (1 ⊗ₜ[R] f x) =
    changeMatrix φ f ((TensorProduct.piScalarRight R S S (Fin a)) (1 ⊗ₜ[R] x))
  simpa only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_one, Function.comp_def] using
    (changeMatrix_apply_map φ f x).symm

/-- 自由列を評価してからテンソル積をとる操作と、行列の係数変更後の評価との自然同型。 -/
noncomputable def evaluationTensorIso (φ : R →+* S) (n : ℕ) :
    evaluation (R := R) (s := s) n ⋙ ModuleCat.extendScalars φ ≅
      changeRing φ ⋙ evaluation n :=
  NatIso.ofComponents (fun X ↦ standardTensorIso φ (X.rank n))
    (fun f ↦ standardTensorIso_naturality φ (f n))

/-- 自由列の複体の係数変更は、各段で実際のテンソル積複体と同型である。 -/
noncomputable def evaluateComplexTensorIso (φ : R →+* S) (n : ℕ)
    (K : CochainComplex (FreeSequence R s) ℤ) :
    baseChange φ ((evaluateComplex n).obj K) ≅
      (evaluateComplex n).obj (((changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) :=
  (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K ≪≫
    (NatIso.mapHomologicalComplex (evaluationTensorIso φ n) (.up ℤ)).app K ≪≫
    ((Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).app K).symm

end SerrePositivity.Asymptotic.FreeSequence
