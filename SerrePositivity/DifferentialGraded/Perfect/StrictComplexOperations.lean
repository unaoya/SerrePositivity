module
public import SerrePositivity.DifferentialGraded.Perfect.StrictComplexEnhancement
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # 既存strictlyPerfectComplexの同型・零対象・次数集中に関する補助API -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 複体の真の同型は有界性と各項の有限射影性を保つ。 -/
lemma strictlyPerfectComplex_of_iso {P Q : Complex A} (e : P ≅ Q)
    (hP : strictlyPerfectComplex A P) : strictlyPerfectComplex A Q := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  refine ⟨⟨a, b, ?_, ?_⟩, ?_⟩
  · exact (Q.isStrictlyGE_iff a).2 (fun i hi =>
      (P.isZero_of_isStrictlyGE a i hi).of_iso ((eval _ _ i).mapIso e).symm)
  · exact (Q.isStrictlyLE_iff b).2 (fun i hi =>
      (P.isZero_of_isStrictlyLE b i hi).of_iso ((eval _ _ i).mapIso e).symm)
  · intro i
    let := (hP.2 i).1
    let := (hP.2 i).2
    let eX : P.X i ≃ₗ[A] Q.X i := ((eval _ _ i).mapIso e).toLinearEquiv
    exact ⟨Module.Finite.equiv eX, Module.Projective.of_equiv' eX⟩

/-- 零対象と同型な複体も既存の有限射影条件を満たす。 -/
lemma strictlyPerfectComplex_of_isZero (P : Complex A) (hP : IsZero P) :
    strictlyPerfectComplex A P :=
  strictlyPerfectComplex_of_iso A hP.isoZero.symm strictlyPerfectComplex_zero

/-- 任意次数に集中する有限射影加群は既存strictlyPerfectComplexである。 -/
lemma strictlyPerfectComplex_single (M : ModuleCat.{u} A) [Module.Finite A M]
    [Module.Projective A M] (n : ℤ) :
    strictlyPerfectComplex A ((single (ModuleCat.{u} A) (.up ℤ) n).obj M) := by
  refine ⟨⟨n, n, inferInstance, inferInstance⟩, ?_⟩
  intro i
  by_cases hi : i = n
  · subst i
    let e := (singleObjXSelf (.up ℤ) n M).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · have hz := isZero_single_obj_X (.up ℤ) n M i hi
    have : Module.Free A (((single (ModuleCat.{u} A) (.up ℤ) n).obj M).X i) :=
      SerrePositivity.isZero_moduleCat_free hz
    exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩

end SerrePositivity.DifferentialGraded
