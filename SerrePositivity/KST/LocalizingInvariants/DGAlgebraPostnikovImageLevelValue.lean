module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveBoundedMapValuePro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageProEquivalence

/-!
概要：有限切断の連結な実レベル表示で、標的比較の値は実 pro 同型である。
方針：像因子分解の下界と全整数群の比較を bounded-below 判定へ渡す。
規約：元の二射・因子分解と同じ中間代数を使う。
使われ方：次数別 pro 連結度から不変量値の連結度への有限段の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
open ProExcision
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

lemma middle_isGE (i : ℕ) : ((middle R X n hn).obj i).X.IsGE (-(n + 1)) := by
  apply (CochainComplex.isGE_iff _ _).2
  intro j hj
  exact (exactAt_iff_isZero_homology _ _).2
    (postnikovImageFactorisationObject_homology_zero R (X.obj i).hom.hom n hn j hj)

lemma right_value_isProIso {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L)
    (h : IsPiProConnected R (original R X) (n + 1)) :
    IsProIso ((right R X n hn).map L) := by
  have htarget (i : ℕ) : ((upperTarget R X n).obj i).X.IsGE (-(n + 1)) := by
    change (postnikov R (X.obj i).right.obj (n + 1)).X.IsGE (-(n + 1))
    have := postnikovComplex_lowerBound R (X.obj i).right.obj (n + 1)
    infer_instance
  exact algebraMap_isProIso_of_bounded_connective R (right R X n hn) L hL (n + 1) (by omega)
    (middle_isConnective R X n hn) (fun i => postnikov_isConnective R (X.obj i).right.obj _)
    (middle_isGE R X n hn) htarget (fun j _ _ => right_piProEquivalence R X n hn h j)

lemma factorisation_level_value {D : Type v} [Category.{w} D]
    (L : Mon (Complex R) ⥤ D) (hL : InvertsConnectiveQuasiIsos R L)
    (h : IsPiProConnected R (original R X) (n + 1)) :
    ((left R X n hn).map L).comp ((right R X n hn).map L) = (upperOriginal R X n).map L ∧
      (∀ i, IsConnected R ((left R X n hn).app i) (n + 1)) ∧
      (∀ i, IsConnective R ((middle R X n hn).obj i)) ∧
      IsProIso ((right R X n hn).map L) := by
  refine ⟨?_, left_connected R X n hn, middle_isConnective R X n hn,
    right_value_isProIso R X n hn L hL h⟩
  rw [← TowerDiagram.levelHom_map_comp, fac]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
