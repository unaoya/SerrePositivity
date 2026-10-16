module
public import SerrePositivity.DifferentialGraded.Complexes.LowerTruncationSequence
public import SerrePositivity.DifferentialGraded.Tensor.KFlatColimits
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex

/-! # 上に有界なflat複体の非有界相手に対するK-flat性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 上に有界な次数ごとflat複体は、任意の非有界acyclic複体とのtensorで消える。 -/
lemma complexKFlat_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i)) :
    complexKFlat A K := by
  have hstage (n : ℕ) : complexKFlat A ((lowerTruncationSequence A K).obj n) := by
    change complexKFlat A (StupidTruncation.above K (-(n : ℤ)))
    apply complexKFlat_of_flat_bounds A _ (-(n : ℤ)) b
    · intro i hi
      exact StupidTruncation.above_isZero_X K _ i hi
    · intro i hi
      by_cases hni : -(n : ℤ) ≤ i
      · exact (StupidTruncation.aboveXIso K _ i hni).isZero_iff.mpr (hb i hi)
      · exact StupidTruncation.above_isZero_X K _ i (by omega)
    · intro i
      by_cases hni : -(n : ℤ) ≤ i
      · have := hflat i
        exact Module.Flat.of_linearEquiv
          (StupidTruncation.aboveXIso K _ i hni).toLinearEquiv
      · have := ModuleCat.subsingleton_of_isZero
          (StupidTruncation.above_isZero_X K (-(n : ℤ)) i (by omega))
        infer_instance
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  exact complexKFlat_of_iso A (lowerTruncationColimitIso A K).symm
    (complexKFlat_colimit A (lowerTruncationSequence A K) hstage)

/-- 上に有界flatな左因子は、相手の有界性なしに任意の準同型を保存する。 -/
lemma complexTensor_quasiIso_right_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) :=
  complexKFlat_quasiIso_right A (complexKFlat_of_flat_boundedAbove A K b hb hflat) f

/-- 上に有界flatな右因子でも、相手の有界性なしに任意の準同型を保存する。 -/
lemma complexTensor_quasiIso_left_of_flat_boundedAbove (K : Complex A) (b : ℤ)
    (hb : ∀ i, b < i → IsZero (K.X i)) (hflat : ∀ i, Module.Flat A (K.X i))
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 K)) :=
  complexKFlat_quasiIso_left A (complexKFlat_of_flat_boundedAbove A K b hb hflat) f

end SerrePositivity.DifferentialGraded
