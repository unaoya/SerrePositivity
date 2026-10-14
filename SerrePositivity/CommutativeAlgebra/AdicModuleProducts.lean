module

public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 有限直積のイデアル進完備性

Mathlib の完備化と有限直積の同型を使い、実際の完備性を供給する。
-/

@[expose] public section
namespace SerrePositivity

/-- 完備加群の有限直積も完備。イデアルの有限生成性・Noether性は不要。 -/
theorem isAdicComplete_function {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (I : Ideal R) [IsAdicComplete I M] : IsAdicComplete I (ι → M) := by
  classical
  let := Fintype.ofFinite ι
  let E := (AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ M)).restrictScalars R
  have hof (f : ι → M) : E (AdicCompletion.of I (ι → M) f) =
      fun i ↦ AdicCompletion.of I M (f i) := by
    funext i
    simp [E, AdicCompletion.pi, AdicCompletion.map_of]
  apply AdicCompletion.of_bijective_iff.mp
  constructor
  · intro f g h
    have he := congrArg E h
    rw [hof, hof] at he
    funext i
    exact AdicCompletion.of_injective I M (congrFun he i)
  · intro x
    let f : ι → M := fun i ↦ (AdicCompletion.ofLinearEquiv I M).symm (E x i)
    refine ⟨f, E.injective ?_⟩
    rw [hof]
    funext i
    exact AdicCompletion.of_ofLinearEquiv_symm I (M := M) (E x i)

end SerrePositivity
