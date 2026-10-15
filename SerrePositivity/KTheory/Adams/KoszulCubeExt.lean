module

public import SerrePositivity.KTheory.Adams.KoszulCubeGenerators
public import SerrePositivity.PerfectComplex.RankOneTensorTripleExt

/-! # Koszul cube maps are detected by the generators in each degree -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulCubeSummand_hom_ext (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (ei : (oneKoszulComplex a).X i ≅ ModuleCat.of R R)
    (ej : (oneKoszulComplex a).X j ≅ ModuleCat.of R R)
    (ek : (oneKoszulComplex a).X k ≅ ModuleCat.of R R)
    {Y : ModuleCat.{u} R} (f g : (tensorCube (oneKoszulComplex a)).X n ⟶ Y)
    (he : oneKoszulCubeGenerator a i j k n h ei.inv ej.inv ek.inv ≫ f =
      oneKoszulCubeGenerator a i j k n h ei.inv ej.inv ek.inv ≫ g) :
    cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        i j k n h ≫ f =
      cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        i j k n h ≫ g := by
  apply rankOneTensorTriple_hom_ext _ _ _ ei ej ek
  have hv := congrArg (fun α => α (1 : R)) he
  change f ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((ei.inv 1 ⊗ₜ[R] ej.inv 1) ⊗ₜ[R] ek.inv 1)) =
    g ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((ei.inv 1 ⊗ₜ[R] ej.inv 1) ⊗ₜ[R] ek.inv 1)) at hv
  simpa only [one_smul, comp_apply] using hv

lemma oneKoszulCubeXZero_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (0) ⟶ Y}
    (h0 : oneKoszulCubeBottom a ≫ f = oneKoszulCubeBottom a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegOne_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-1) ⟶ Y}
    (h0 : oneKoszulCubeE0 a ≫ f = oneKoszulCubeE0 a ≫ g)
    (h1 : oneKoszulCubeE1 a ≫ f = oneKoszulCubeE1 a ≫ g)
    (h2 : oneKoszulCubeE2 a ≫ f = oneKoszulCubeE2 a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0 | exact h1 | exact h2
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegTwo_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h0 : oneKoszulCubeE01 a ≫ f = oneKoszulCubeE01 a ≫ g)
    (h1 : oneKoszulCubeE02 a ≫ f = oneKoszulCubeE02 a ≫ g)
    (h2 : oneKoszulCubeE12 a ≫ f = oneKoszulCubeE12 a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0 | exact h1 | exact h2
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegThree_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-3) ⟶ Y}
    (h0 : oneKoszulCubeTop a ≫ f = oneKoszulCubeTop a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (oneKoszulXNegOneIso a)
              (oneKoszulXNegOneIso a)
              (oneKoszulXNegOneIso a)
            first | exact h0
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

end Adams
end SerrePositivity
