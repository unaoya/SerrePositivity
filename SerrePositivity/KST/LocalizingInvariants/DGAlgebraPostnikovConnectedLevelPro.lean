module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovConnectedLevel

/-!
概要：元の未切断の標的へのレベル比較は、全整数群と全有限切断で pro 同値である。
方針：像模型の比較を実 pullback の二隣接次数の判定へ渡し、cover の同型を反映する。
規約：一般 pro ∞ 圏での同値とは同一視しない。
使われ方：元の塔を持つ連結なレベル表示の比較脚と実有限切断逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
open ProExcision
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

private lemma negative_groups_subsingleton (A : NonpositiveAlgebra R) (j : ℤ) (hj : j < 0) :
    Subsingleton ((groups R j).obj A.obj) := by
  have : A.obj.X.IsStrictlyLE 0 := A.property
  apply groups_subsingleton_of_homology_zero
  exact A.obj.X.isZero_of_isLE 0 (-j) (by omega)

lemma right_piProEquivalence
    (h : IsPiProConnected R (PostnikovImagePro.original R X) (n + 1)) :
    IsPiProEquivalence R ((right R X n hn).map (nonpositiveInclusion R)) := by
  intro j
  by_cases hj : 0 ≤ j
  · have hp := PostnikovImagePro.right_piProEquivalence R X n hn h
    have hraw := HomotopyPullbackModel.rightProjection_groups_isProIso R
      (PostnikovImagePro.right R X n hn) (PostnikovImagePro.targetQuotient R X n) j
      (hp (j + 1)) (hp j)
    have hcover : IsProIso ((coverTowerCounit R (rawMiddle R X n hn)).map (groups R j)) := by
      have : ∀ i, IsIso (((coverTowerCounit R (rawMiddle R X n hn)).map (groups R j)).app i) :=
        fun i => connectiveCoverInclusion_groups_isIso R _ j hj
      exact TowerDiagram.isProIso_of_levelwiseIso _
    change IsProIso (((coverTowerCounit R (rawMiddle R X n hn)).comp
      (rawRight R X n hn)).map (groups R j))
    rw [TowerDiagram.levelHom_map_comp]
    exact hcover.comp hraw
  · have : ∀ i, IsIso ((((right R X n hn).map (nonpositiveInclusion R)).map
        (groups R j)).app i) := by
      intro i
      have : Subsingleton ((((middle R X n hn).map (nonpositiveInclusion R)).map
          (groups R j)).obj i) := negative_groups_subsingleton R ((middle R X n hn).obj i) j
            (by omega)
      have : Subsingleton ((((target R X).map (nonpositiveInclusion R)).map
          (groups R j)).obj i) := negative_groups_subsingleton R ((target R X).obj i) j (by omega)
      apply (ConcreteCategory.isIso_iff_bijective _).2
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
    exact TowerDiagram.isProIso_of_levelwiseIso _

lemma right_finite_value_isProIso
    (h : IsPiProConnected R (PostnikovImagePro.original R X) (n + 1))
    (cutoff : ℤ) (hc : 0 ≤ cutoff) {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L) :
    IsProIso (((right R X n hn).map (postnikovFunctor R cutoff)).map L) :=
  postnikovFiniteMap_isProIso_of_connective R cutoff hc (right R X n hn) L
    (fun j _ _ => right_piProEquivalence R X n hn h j) hL

lemma right_finite_actual_inverse
    (h : IsPiProConnected R (PostnikovImagePro.original R X) (n + 1))
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R
        ((right R X n hn).map (postnikovFunctor R cutoff)) i m hi) :=
  postnikovFiniteMap_exists_nonpositiveInverseRoof_int R cutoff hc (right R X n hn)
    (fun j _ _ => right_piProEquivalence R X n hn h j) i

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovConnectedLevel
