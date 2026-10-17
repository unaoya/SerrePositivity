module
public import SerrePositivity.DifferentialGraded.Perfect.RingFiniteHomologyCover
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # 射影的上端を取り除く良い切断

上端の微分が全射なら、その核は有限射影項の直和因子である。
良い切断により一段短い有限射影複体を得る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ringComplex_cycles_finite_projective_of_epi (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] [Module.Projective A (P.X n)]
    [Module.Projective A (P.X (n + 1))] [Epi (P.d n (n + 1))] :
    Module.Finite A (P.cycles n) ∧ Module.Projective A (P.cycles n) := by
  let d := P.d n (n + 1)
  let s := Projective.factorThru (𝟙 (P.X (n + 1))) d
  have hs : s ≫ d = 𝟙 _ := Projective.factorThru_comp _ _
  let q := P.liftCycles (𝟙 (P.X n) - d ≫ s) (n + 1) (by simp) (by
    change (𝟙 (P.X n) - d ≫ s) ≫ d = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self])
  have hq : P.iCycles n ≫ q = 𝟙 _ := by
    apply (cancel_mono (P.iCycles n)).1
    rw [Category.assoc, liftCycles_i, Category.id_comp, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc]
    have h : P.iCycles n ≫ d = 0 := P.iCycles_d n (n + 1)
    rw [h, zero_comp, sub_zero]
  let a : Retract (P.cycles n) (P.X n) := ⟨P.iCycles n, q, hq⟩
  exact ⟨finiteModule_of_retract A a,
    Module.Projective.of_split (P.iCycles n).hom q.hom (congrArg (fun f => f.hom) hq)⟩

lemma ringComplex_truncLE_strictlyGE (P : Complex A) (a n : ℤ) (han : a ≤ n)
    [P.IsStrictlyGE a] : (P.truncLE n).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (P.isZero_of_isStrictlyGE a i hi).of_iso (P.truncLEXIso n i (by omega))

lemma ringComplex_truncLE_strictlyPerfect_of_epi (P : Complex A)
    (hP : strictlyPerfectComplex A P) (n : ℤ) [Epi (P.d n (n + 1))] :
    strictlyPerfectComplex A (P.truncLE n) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  have : P.IsStrictlyGE (min a n) := P.isStrictlyGE_of_ge (min a n) a (min_le_left _ _)
  have : (P.truncLE n).IsStrictlyGE (min a n) :=
    ringComplex_truncLE_strictlyGE A P (min a n) n (min_le_right _ _)
  refine ⟨⟨min a n, n, inferInstance, inferInstance⟩, fun i => ?_⟩
  rcases lt_trichotomy i n with hi | hi | hi
  · let := (hP.2 i).1
    let := (hP.2 i).2
    let e := (P.truncLEXIso n i hi).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · subst i
    let := (hP.2 n).1
    let := (hP.2 n).2
    let := (hP.2 (n + 1)).2
    obtain ⟨hf, hp⟩ := ringComplex_cycles_finite_projective_of_epi A P n
    let := hf
    let := hp
    let e := (P.truncLEXIsoCycles n).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · have hz := (P.truncLE n).isZero_of_isStrictlyLE n i hi
    have : Module.Free A ((P.truncLE n).X i) := SerrePositivity.isZero_moduleCat_free hz
    exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩

lemma ringComplex_truncLE_quasiIso_of_top_exact (P : Complex A) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) : QuasiIso (P.ιTruncLE n) := by
  have : P.IsLE n := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    by_cases he : i = n + 1
    · simpa only [he] using h
    · exact P.exactAt_of_isLE (n + 1) i (by omega)
  infer_instance

lemma ringComplex_d_epi_of_top_exact (P : Complex A) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) : Epi (P.d n (n + 1)) := by
  have h' : (P.sc' n (n + 1) (n + 2)).Exact :=
    (P.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).1 h
  exact h'.epi_f ((P.isZero_of_isStrictlyLE (n + 1) (n + 2) (by omega)).eq_of_tgt _ _)

lemma ringComplex_topTruncation (P : Complex A) (hP : strictlyPerfectComplex A P) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) :
    strictlyPerfectComplex A (P.truncLE n) ∧ QuasiIso (P.ιTruncLE n) := by
  let := ringComplex_d_epi_of_top_exact A P n h
  exact ⟨ringComplex_truncLE_strictlyPerfect_of_epi A P hP n,
    ringComplex_truncLE_quasiIso_of_top_exact A P n h⟩

end SerrePositivity.DifferentialGraded
