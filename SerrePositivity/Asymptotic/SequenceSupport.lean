module

public import SerrePositivity.Asymptotic.SequenceLinear
public import SerrePositivity.CategoryTheory.ScalarSupport
public import SerrePositivity.PerfectComplex.ResolutionFamilies

/-!
# 自由列の台と共通の零ホモトピー

自由列の圏での零ホモトピーは、各段で独立に選んだ零ホモトピーを組み戻せる。
したがって台の条件に必要なのは消去指数の一様性であり、ホモトピーの係数の有界性ではない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {s : ℕ → ℕ}

/-- 共通有界複体を共通有界ホモトピー圏の対象とみなす。 -/
def sequenceHomotopyObj (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) : SequenceHomotopy R s :=
  ⟨(HomotopyCategory.quotient _ _).obj F, (boundedHomotopyProperty_quotient _ F).2 hF⟩

/-- ホモトピー圏でスカラー作用が零であることは、各段で零ホモトピックなことと同値。 -/
lemma sequence_smul_id_zero_iff
    (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) (a : R) :
    a • 𝟙 (sequenceHomotopyObj F hF) = 0 ↔
      ∀ n, Nonempty (Homotopy (a • 𝟙 ((evaluateComplex n).obj F)) 0) := by
  have h : a • 𝟙 (sequenceHomotopyObj F hF) = 0 ↔
      (HomotopyCategory.quotient _ _).map (a • 𝟙 F) =
        (HomotopyCategory.quotient _ _).map (0 : F ⟶ F) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero]
    exact ⟨fun h ↦ congrArg (fun f ↦ f.hom) h, fun h ↦ ObjectProperty.hom_ext _ h⟩
  rw [h, quotient_map_eq_iff_pointwise]
  apply forall_congr'
  intro n
  simp only [Functor.map_zero, HomotopyCategory.quotient_map_eq_zero_iff]
  have : (evaluateComplex (R := R) (s := s) n).Linear R := by
    change ((FreeSequence.evaluation (R := R) (s := s) n).mapHomologicalComplex (.up ℤ)).Linear R
    infer_instance
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id]

/-- 台をもつことは、全段に共通の正の指数による零ホモトピーの存在と同値。 -/
lemma sequence_supported_iff {ι : Type*} (z : ι → R)
    (F : CochainComplex (FreeSequence R s) ℤ)
    (hF : strictlyBoundedComplex (FreeSequence R s) F) :
    scalarSupported z (sequenceHomotopyObj F hF) ↔
      ∃ v : ℕ, 0 < v ∧ ∀ j n,
        Nonempty (Homotopy (z j ^ v • 𝟙 ((evaluateComplex n).obj F)) 0) := by
  simp only [scalarSupported, sequence_smul_id_zero_iff]

/-- 共通範囲 `[-d,0]` の分解では、加群列の共通の消去指数から列全体の台が得られる。 -/
lemma sequence_resolution_supported {ι : Type*} (z : ι → R)
    (F : CochainComplex (FreeSequence R s) ℤ) (d : ℕ)
    (ha : F.IsStrictlyGE (-(d : ℤ))) (hb : F.IsStrictlyLE 0)
    (M : ℕ → ModuleCat.{u} R)
    (hres : ∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M n)))
    (N : ℕ) (hN : 0 < N) (hM : ∀ n j, z j ^ N • 𝟙 (M n) = 0) :
    scalarSupported z (sequenceHomotopyObj F ⟨-(d : ℤ), 0, ha, hb⟩) := by
  apply (sequence_supported_iff _ _ _).2
  refine ⟨N * (d + 1), Nat.mul_pos hN (by omega), fun j n ↦ ?_⟩
  apply resolutionFamily_uniform_nullHomotopies M (fun n ↦ (evaluateComplex n).obj F)
    hres d ?_ z N hM n j
  intro n i hi
  rcases hi with hi | hi
  · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyGE _ i hi)
  · exact (FreeSequence.evaluation n).map_isZero (F.isZero_of_isStrictlyLE _ i hi)

end SerrePositivity.Asymptotic
