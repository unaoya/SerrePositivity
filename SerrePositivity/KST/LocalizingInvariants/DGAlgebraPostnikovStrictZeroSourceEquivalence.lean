module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroSourcePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroBaseHomology

/-!
概要：底を揃えた元の源射の、有限範囲の群の仮定から全整数 π-pro 同値を得る。
方針：零次数の各段同型・正の保持範囲・両側の厳密次数消滅を組み合わせる。
規約：実代数 pro 逆や一般 pro ∞ 同値とは主張しない。使われ方：源側の逆 roof の条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

lemma postnikovStrictZeroBase_groups_subsingleton_high (j : ℤ) (hj : n < j) (i : ℕ) :
    Subsingleton (((postnikovStrictZeroBaseTower R f n hn).map (groups R j)).obj i) := by
  have := postnikovStrictZeroBase_lowerBound R f n hn i
  apply groups_subsingleton_of_homology_zero R _ j
  exact ((postnikovStrictZeroBaseTower R f n hn).obj i).X.isZero_of_isGE (-n) (-j) (by omega)

lemma postnikovStrictZeroBase_groups_subsingleton_negative (j : ℤ) (hj : j < 0) (i : ℕ) :
    Subsingleton (((postnikovStrictZeroBaseTower R f n hn).map (groups R j)).obj i) := by
  have := postnikovStrictZeroBase_nonpositive R f n hn i
  apply groups_subsingleton_of_homology_zero R _ j
  exact ((postnikovStrictZeroBaseTower R f n hn).obj i).X.isZero_of_isLE 0 (-j) (by omega)

lemma postnikovStrictZeroBaseLift_piProEquivalence
    (hf : ∀ j : ℤ, 0 < j → j ≤ n →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) :
    IsPiProEquivalence R (postnikovStrictZeroBaseLift R f n hn) := by
  intro j
  by_cases h₀ : j = 0
  · subst j
    have : ∀ i, IsIso (((postnikovStrictZeroBaseLift R f n hn).map (groups R 0)).app i) :=
      postnikovStrictZeroBaseLift_groups_zero_isIso R f n hn
    exact TowerDiagram.isProIso_of_levelwiseIso _
  by_cases hj : 0 < j
  · by_cases hjn : j ≤ n
    · exact postnikovStrictZeroBaseLift_groups_proIso R f n hn j hj hjn (hf j hj hjn)
    · apply ProGroup.proIso_of_cofinal_bijective
      intro i
      have : Subsingleton (((A.map (postnikovFunctor R n)).map (groups R j)).obj i) :=
        postnikov_groups_subsingleton R (A.obj i).obj n j (by omega)
      have := postnikovStrictZeroBase_groups_subsingleton_high R f n hn j (by omega) i
      exact ⟨i, le_refl i, Function.injective_of_subsingleton _,
        Function.surjective_to_subsingleton _⟩
  · apply ProGroup.proIso_of_cofinal_bijective
    intro i
    have hA : (postnikov R (A.obj i).obj n).X.IsLE 0 :=
      postnikov_isConnective R (A.obj i).obj n
    have : Subsingleton (((A.map (postnikovFunctor R n)).map (groups R j)).obj i) :=
      groups_subsingleton_of_homology_zero R (postnikov R (A.obj i).obj n) j
      ((postnikov R (A.obj i).obj n).X.isZero_of_isLE 0 (-j) (by omega))
    have := postnikovStrictZeroBase_groups_subsingleton_negative R f n hn j (by omega) i
    exact ⟨i, le_refl i, Function.injective_of_subsingleton _,
      Function.surjective_to_subsingleton _⟩

/-- n=1 の源側は、元の π₁ の pro 同型だけで全整数の群の比較を満たす。 -/
lemma postnikovStrictZeroBaseLift_one_piProEquivalence
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    IsPiProEquivalence R (postnikovStrictZeroBaseLift R f 1 (by omega)) := by
  apply postnikovStrictZeroBaseLift_piProEquivalence R f 1 (by omega)
  intro j hj hjn
  have he : j = 1 := by omega
  subst j
  exact hf

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
