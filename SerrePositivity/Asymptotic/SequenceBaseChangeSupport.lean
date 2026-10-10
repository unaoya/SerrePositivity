module

public import SerrePositivity.Asymptotic.FreeSequenceTensor
public import SerrePositivity.Asymptotic.SequenceSupport
public import SerrePositivity.Asymptotic.RankQuotientBaseChange

/-!
# 自由複体列の係数変更と一様な台

行列の係数変更はスカラー倍を環準同型に沿って移す。
従って、列全体を消す共通の冪と零ホモトピーを係数変更後も使える。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S] {s : ℕ → ℕ}

/-- 一様に台をもつ自由複体列の各段は、有限版3.5で用いる台つき完全複体である。 -/
lemma evaluateComplex_isPerfectSupported {e : ℕ} (z : Fin e → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : scalarSupported z (sequenceHomotopyObj K hK)) (n : ℕ) :
    IsPerfectSupported z ((evaluateComplex n).obj K) := by
  obtain ⟨v, hv, hn⟩ := (sequence_supported_iff z K hK).mp hzK
  obtain ⟨a, b, ha, hb⟩ := hK
  refine ⟨⟨a, b, fun i hi ↦ ?_⟩, fun i ↦ ?_, fun i ↦ ?_, ⟨v, fun j ↦ hn j n⟩⟩
  · apply (FreeSequence.evaluation n).map_isZero
    rcases hi with hi | hi
    · exact K.isZero_of_isStrictlyGE a i hi
    · exact K.isZero_of_isStrictlyLE b i hi
  · exact inferInstanceAs (Module.Free R (Fin ((K.X i).rank n) → R))
  · exact inferInstanceAs (Module.Finite R (Fin ((K.X i).rank n) → R))

/-- 行列の係数変更は環準同型に沿ってスカラー倍を保つ。 -/
lemma FreeSequence.changeMatrix_smul (φ : R →+* S) {a b : ℕ}
    (r : R) (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    FreeSequence.changeMatrix φ (r • f) = φ r • FreeSequence.changeMatrix φ f := by
  apply Matrix.toLin'.symm.injective
  simp only [FreeSequence.changeMatrix, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_smul]
  ext i j
  simp [Matrix.map_apply, smul_eq_mul, map_mul]

/-- 複体列の係数変更の射への作用もスカラー倍と両立する。 -/
lemma changeRing_complex_map_smul (φ : R →+* S)
    {K L : CochainComplex (FreeSequence R s) ℤ} (r : R) (f : K ⟶ L) :
    ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map (r • f) =
      φ r • ((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).map f := by
  apply HomologicalComplex.Hom.ext
  funext q
  funext n
  exact FreeSequence.changeMatrix_smul φ r (f.f q n)

/-- 共通有界性は係数変更後にも保たれる。 -/
lemma changeRing_strictlyBounded (φ : R →+* S)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K) :
    strictlyBoundedComplex (FreeSequence S s)
      (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  obtain ⟨a, b, ha, hb⟩ := hK
  exact ⟨a, b, inferInstance, inferInstance⟩

/-- 共通の冪による台は、自由複体列の係数変更で保たれる。 -/
lemma changeRing_complex_supported (φ : R →+* S) {ι : Type*} (z : ι → R)
    (K : CochainComplex (FreeSequence R s) ℤ)
    (hK : strictlyBoundedComplex (FreeSequence R s) K)
    (hzK : scalarSupported z (sequenceHomotopyObj K hK)) :
    scalarSupported (φ ∘ z)
      (sequenceHomotopyObj (((FreeSequence.changeRing φ).mapHomologicalComplex (.up ℤ)).obj K)
        (changeRing_strictlyBounded φ K hK)) := by
  obtain ⟨v, hv, hzero⟩ := hzK
  refine ⟨v, hv, fun j ↦ ?_⟩
  have hq : (HomotopyCategory.quotient _ _).map (z j ^ v • 𝟙 K) = 0 := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
    exact congrArg (fun f ↦ f.hom) (hzero j)
  obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).mp hq
  have hm := (FreeSequence.changeRing φ).mapHomotopy H
  rw [changeRing_complex_map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at hm
  have hh := (HomotopyCategory.quotient_map_eq_zero_iff _).mpr ⟨hm⟩
  rw [Functor.map_smul, CategoryTheory.Functor.map_id, map_pow] at hh
  exact ObjectProperty.hom_ext _ hh

end SerrePositivity.Asymptotic
