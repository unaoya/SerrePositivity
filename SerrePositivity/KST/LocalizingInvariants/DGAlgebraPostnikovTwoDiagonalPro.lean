module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackDiagonalPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMapProGroups
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology

/-!
概要：元の三次数の pro 同型から、二切断自己 cospan の実対角の同じ比較を導く。
方針：切断商の自然性で三次数を移し、消滅する第三群と実 cocone 完全列を使う。
規約：対角の pro 比較を追加入力しない。使われ方：実左三角形の対角反映。
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
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

abbrev postnikovTwoRawDiagonal := HomotopyPullbackModel.diagonalHom R
  (f.map (postnikovFunctor R 2))

lemma postnikovTwoMap_third_groups_proIso :
    IsProIso ((f.map (postnikovFunctor R 2)).map (groups R 3)) := by
  have hz (C : NonpositiveAlgebra R) :
      Subsingleton ((groups R 3).obj (postnikov R C.obj 2)) := by
    have : (postnikov R C.obj 2).X.IsStrictlyGE (-2) :=
      postnikovComplex_lowerBound R C.obj 2
    apply groups_subsingleton_of_homology_zero
    exact (postnikov R C.obj 2).X.isZero_of_isGE (-2) (-3) (by omega)
  have : ∀ i, IsIso (((f.map (postnikovFunctor R 2)).map (groups R 3)).app i) := by
    intro i
    letI : Subsingleton (((A.map (postnikovFunctor R 2)).map (groups R 3)).obj i) :=
      hz (A.obj i)
    letI : Subsingleton (((B.map (postnikovFunctor R 2)).map (groups R 3)).obj i) :=
      hz (B.obj i)
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
  exact TowerDiagram.isProIso_of_levelwiseIso _

lemma postnikovTwoRawDiagonal_groups_proIso
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2)))
    (j : ℤ) (hj : 0 ≤ j) (hj₂ : j ≤ 2) :
    IsProIso ((postnikovTwoRawDiagonal R f).map (groups R j)) := by
  have h0 := postnikovMap_groups_proIso R f 2 0 (by omega) h₀
  have h1 := postnikovMap_groups_proIso R f 2 1 (by omega) h₁
  have h2 := postnikovMap_groups_proIso R f 2 2 (by omega) h₂
  have h3 := postnikovTwoMap_third_groups_proIso R f
  interval_cases j
  · exact HomotopyPullbackModel.diagonal_groups_isProIso R _ 0 h1 h0
  · exact HomotopyPullbackModel.diagonal_groups_isProIso R _ 1 h2 h1
  · exact HomotopyPullbackModel.diagonal_groups_isProIso R _ 2 h3 h2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
