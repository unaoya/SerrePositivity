module
public import SerrePositivity.DifferentialGraded.Complexes.Closed

/-! # パラメータ複体の射に関する逆転置と二重転置 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A : Type u} [CommRing A]

lemma uncurryRight_precompose {K L P T : Complex A} (g : L ⟶ K)
    (f : K ⟶ homComplex A P T) :
    uncurryRight (g ≫ f) = (g ▷ P) ≫ uncurryRight f := by
  apply (tensorRightHomEquiv P L T).injective
  change curryRight (uncurryRight (g ≫ f)) = curryRight ((g ⊗ₘ 𝟙 P) ≫ uncurryRight f)
  rw [curryRight_uncurryRight, curryRight_naturality_source, curryRight_uncurryRight]

lemma curryRight_twice_precompose {K L P Q T : Complex A} (g : L ⟶ K)
    (f : (K ⊗ P) ⊗ Q ⟶ T) :
    g ≫ curryRight (curryRight f) = curryRight (curryRight (((g ▷ P) ▷ Q) ≫ f)) := by
  rw [← curryRight_naturality_source, ← curryRight_naturality_source]
  rfl

end SerrePositivity.DifferentialGraded
