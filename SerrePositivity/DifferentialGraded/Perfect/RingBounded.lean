module
public import SerrePositivity.DifferentialGraded.Perfect.RingExtensions
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexProjective

/-! # 有界有限射影複体の主導来perfect性

下端項への射影の核で有限幅を一つ減らす。短完全列と次数集中複体の比較は既存APIを使う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 有限の次数範囲にある各項有限射影の複体の主導来像はperfect。 -/
lemma ringComplexDerived_perfect_of_finite_range (w : ℕ) (a : ℤ) (P : Complex A)
    (hterm : ∀ i, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i))
    (hb : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i)) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  induction w generalizing a P with
  | zero =>
    have hz : IsZero P := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext i
      exact (hb i (by omega)).eq_of_src _ _
    have hZ := (complexToRingModule A ⋙ moduleToDerived A PUnit.{1}).map_isZero hz
    exact (modulePerfect A PUnit.{1}).prop_of_iso hZ.isoZero.symm
      (modulePerfectOver_zero A PUnit.{1} Set.univ)
  | succ w ih =>
    let ha := fun i (hi : i < a) => hb i (Or.inl hi)
    let π := SerrePositivity.bottomProjection P a ha
    let P' := kernel π
    have : Epi π := SerrePositivity.bottomProjection_epi P a ha
    let S : ShortComplex (Complex A) := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    have hb' : ∀ i, (i < a + 1 ∨ a + 1 + w ≤ i) → IsZero (P'.X i) := by
      intro i hi
      by_cases hia : i = a
      · subst i
        exact SerrePositivity.bottomProjection_kernel_isZero P a ha
      · exact (hb i (by omega)).of_iso
          (SerrePositivity.bottomProjectionKernelXIso P a ha i hia)
    have ht' : ∀ i, Module.Finite A (P'.X i) ∧ Module.Projective A (P'.X i) := by
      intro i
      by_cases hia : i = a
      · subst i
        have hz := SerrePositivity.bottomProjection_kernel_isZero P a ha
        have : Module.Free A (P'.X a) := SerrePositivity.isZero_moduleCat_free hz
        exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩
      · let := (hterm i).1
        let := (hterm i).2
        let e := (SerrePositivity.bottomProjectionKernelXIso P a ha i hia).toLinearEquiv
        exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
    let := (hterm a).1
    let := (hterm a).2
    exact ringComplexDerived_perfect_of_shortExact A S hS (ih (a + 1) P' ht' hb')
      (ringSingleToDerived_finiteProjective_perfect A a (P.X a))

/-- 既存strictlyPerfectComplexの主dg加群導来像は主Perfに入る。 -/
lemma strictlyPerfectComplex_ringDerived_perfect (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  apply ringComplexDerived_perfect_of_finite_range A (b - a + 1).toNat a P hP.2
  intro i hi
  rcases hi with hi | hi
  · exact P.isZero_of_isStrictlyGE a i hi
  · exact P.isZero_of_isStrictlyLE b i (by omega)

end SerrePositivity.DifferentialGraded
