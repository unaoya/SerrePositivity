module

public import SerrePositivity.Asymptotic.AssembleComplex
public import SerrePositivity.PerfectComplex.ResolutionFamilies
public import Mathlib.LinearAlgebra.StdBasis

/-!
# 有限長加群列の自由列による分解

長さが `O(s)` の有限長加群列を、自由列の圏の実際の共通有界複体で分解する。
剰余体の固定した有限自由分解を入力とし、項のランク公式と次数範囲を保持する。
この結果は heart の対象の持ち上げであり、商の任意の対象の持ち上げではない。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory CategoryTheory.Limits IsLocalRing Filter Asymptotics

variable {A : Type u} [CommRing A] [IsLocalRing A] {s : ℕ → ℕ}

/-- 長さ `O(s)` の有限長加群列は、共通範囲 `[-d,0]` の自由列の複体で分解できる。
ランクは長さと剰余体の固定分解のランクの積である。 -/
theorem exists_sequence_resolution
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
    (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
    (d : ℕ) (hKb : ∀ i, i < -(d : ℤ) → IsZero (K.X i))
    (M : ℕ → ModuleCat.{u} A) (hM : ∀ n, IsFiniteLength A (M n))
    (hbound : (fun n ↦ ((Module.length A (M n)).toNat : ℝ)) =O[atTop]
      (fun n ↦ (s n : ℝ))) :
    ∃ F : CochainComplex (FreeSequence A s) ℤ,
      (F.IsStrictlyGE (-(d : ℤ)) ∧ F.IsStrictlyLE 0) ∧
      (∀ n, Nonempty (IsResolutionOf ((evaluateComplex n).obj F) (M n))) ∧
      ∀ i n, (F.X i).rank n =
        (Module.length A (M n)).toNat * Module.finrank A (K.X i) := by
  obtain ⟨P, hres, hfree, hfinite, hb, hrank⟩ :=
    exists_uniform_free_resolutions K hK hKf hKn d hKb M hM
  let r (i : ℤ) (n : ℕ) := Module.finrank A ((P n).X i)
  have hr (i : ℤ) : (fun n ↦ (r i n : ℝ)) =O[atTop] (fun n ↦ (s n : ℝ)) :=
    resolutionFamily_rank_isBigO K M P hrank _ hbound i
  let e (n : ℕ) (i : ℤ) : ModuleCat.of A (Fin (r i n) → A) ≅ (P n).X i := by
    have := hfree n i
    have := hfinite n i
    exact (Module.finBasis A ((P n).X i)).equivFun.toModuleIso.symm
  let F := assembleComplex P r hr e
  have hzero (i : ℤ) (hi : i < -(d : ℤ) ∨ 0 < i) : IsZero (F.X i) := by
    apply (IsZero.iff_id_eq_zero _).2
    funext n
    exact congrArg ModuleCat.Hom.hom
      (((hb n i hi).of_iso (e n i)).eq_of_src
        (𝟙 (ModuleCat.of A (Fin (r i n) → A))) 0)
  refine ⟨F, ⟨(CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi ↦ hzero i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi ↦ hzero i (.inr hi))⟩,
    ?_, fun i n ↦ hrank n i⟩
  intro n
  let en := evaluateAssembleIso P r hr e n
  let hn := (hres n).some
  refine ⟨{ isZero_X := fun i hi ↦ (hn.isZero_X i hi).of_iso (e n i)
            projective := fun i ↦ ModuleCat.projective_of_free (Pi.basisFun A (Fin (r i n)))
            isZero_homology := fun i hi ↦ (hn.isZero_homology i hi).of_iso
              ((HomologicalComplex.homologyFunctor _ _ i).mapIso en)
            homologyZeroIso :=
              (HomologicalComplex.homologyFunctor _ _ 0).mapIso en ≪≫ hn.homologyZeroIso }⟩

end SerrePositivity.Asymptotic
