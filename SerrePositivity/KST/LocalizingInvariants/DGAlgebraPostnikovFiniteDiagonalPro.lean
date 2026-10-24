module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackDiagonalPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMapProGroups
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProHomology

/-!
概要：有限範囲の pro 同型から、同じ有限切断の実対角の pro 同型を導く。
方針：切断の上の群の消滅と、実 cocone 完全列による対角比較を組み合わせる。
規約：対角の pro 比較を追加入力にしない。切断次数は整数 n。
使われ方：有限 Postnikov 帰納での左欠損の対角反映。
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
variable (R : Type u) [CommRing R] (n : ℤ)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

abbrev postnikovFiniteRawDiagonal := HomotopyPullbackModel.diagonalHom R
  (f.map (postnikovFunctor R n))

lemma postnikovFiniteMap_above_groups_proIso (j : ℤ) (hj : n < j) :
    IsProIso ((f.map (postnikovFunctor R n)).map (groups R j)) := by
  have hz (C : NonpositiveAlgebra R) :
      Subsingleton ((groups R j).obj (postnikov R C.obj n)) := by
    have : (postnikov R C.obj n).X.IsStrictlyGE (-n) := postnikovComplex_lowerBound R C.obj n
    apply groups_subsingleton_of_homology_zero
    exact (postnikov R C.obj n).X.isZero_of_isGE (-n) (-j) (by omega)
  have : ∀ i, IsIso (((f.map (postnikovFunctor R n)).map (groups R j)).app i) := by
    intro i
    letI : Subsingleton (((A.map (postnikovFunctor R n)).map (groups R j)).obj i) := hz (A.obj i)
    letI : Subsingleton (((B.map (postnikovFunctor R n)).map (groups R j)).obj i) := hz (B.obj i)
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
  exact TowerDiagram.isProIso_of_levelwiseIso _

lemma postnikovFiniteRawDiagonal_groups_proIso
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ n →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j)))
    (j : ℤ) (hj : 0 ≤ j) (hjn : j ≤ n) :
    IsProIso ((postnikovFiniteRawDiagonal R n f).map (groups R j)) := by
  have hsame := postnikovMap_groups_proIso R f n j hjn (h j hj hjn)
  have hnext : IsProIso ((f.map (postnikovFunctor R n)).map (groups R (j + 1))) := by
    by_cases he : j + 1 ≤ n
    · exact postnikovMap_groups_proIso R f n (j + 1) he (h (j + 1) (by omega) he)
    · exact postnikovFiniteMap_above_groups_proIso R n f (j + 1) (by omega)
  exact HomotopyPullbackModel.diagonal_groups_isProIso R _ j hnext hsame

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
