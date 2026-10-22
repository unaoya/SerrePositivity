module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageProDiagram
public import SerrePositivity.KST.LocalizingInvariants.ProGroupImageSurjectivity
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumEventualConnectivity

/-!
概要：固定した実因子分解の標的レベル射を、低次数・新しい層・高次数で pro 同型判定する。
方針：元の商射の同型比較、源射の低次数同型と新しい層の全射・単射、高次数消滅を使う。
規約：元の群の塔の実射を保持。使われ方：有限 Postnikov 模型の次数別 π-pro 同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
open ProExcision
variable (R : Type u) [CommRing R] (X : Tower (Arrow (NonpositiveAlgebra R)))
  (n : ℤ) (hn : 0 ≤ n)

lemma groups_quotient_square (j : ℤ) :
    ((original R X).map (groups R j)).comp ((targetQuotient R X n).map (groups R j)) =
      ((sourceQuotient R X n).map (groups R j)).comp ((upperOriginal R X n).map (groups R j)) := by
  rw [← TowerDiagram.levelHom_map_comp, quotient_square, TowerDiagram.levelHom_map_comp]

lemma groups_fac (j : ℤ) :
    ((left R X n hn).map (groups R j)).comp ((right R X n hn).map (groups R j)) =
      (upperOriginal R X n).map (groups R j) := by
  rw [← TowerDiagram.levelHom_map_comp, fac]

lemma upperOriginal_groups_proIso (j : ℤ) (hj : j ≤ n + 1)
    (h : IsProIso ((original R X).map (groups R j))) :
    IsProIso ((upperOriginal R X n).map (groups R j)) := by
  have : ∀ i, IsIso (((sourceQuotient R X n).map (groups R j)).app i) :=
    sourceQuotient_groups_isIso R X n j hj
  have : ∀ i, IsIso (((targetQuotient R X n).map (groups R j)).app i) :=
    targetQuotient_groups_isIso R X n j hj
  exact TowerDiagram.proIso_of_square ((original R X).map (groups R j))
    ((upperOriginal R X n).map (groups R j)) ((sourceQuotient R X n).map (groups R j))
    ((targetQuotient R X n).map (groups R j)) (groups_quotient_square R X n j) h

lemma upperOriginal_groups_eventual_image (j : ℤ) (hj : j ≤ n + 1)
    (h : ProGroup.IsEventuallyImageSurjective ((original R X).map (groups R j))) :
    ProGroup.IsEventuallyImageSurjective ((upperOriginal R X n).map (groups R j)) := by
  apply ProGroup.imageSurjective_of_square ((original R X).map (groups R j))
    ((upperOriginal R X n).map (groups R j)) ((sourceQuotient R X n).map (groups R j))
    ((targetQuotient R X n).map (groups R j)) (groups_quotient_square R X n j) ?_ h
  intro i
  have := targetQuotient_groups_isIso R X n j hj i
  exact (ConcreteCategory.bijective_of_isIso _).2

lemma right_groups_proIso_low (j : ℤ) (hj : j ≤ n)
    (h : IsProIso ((original R X).map (groups R j))) :
    IsProIso ((right R X n hn).map (groups R j)) := by
  have : ∀ i, IsIso (((left R X n hn).map (groups R j)).app i) := left_groups_isIso R X n hn j hj
  apply TowerDiagram.proIso_of_comp_left_levelwiseIso ((left R X n hn).map (groups R j))
    ((right R X n hn).map (groups R j))
  rw [groups_fac]
  exact upperOriginal_groups_proIso R X n j (by omega) h

lemma right_groups_proIso_succ
    (h : ProGroup.IsEventuallyImageSurjective ((original R X).map (groups R (n + 1)))) :
    IsProIso ((right R X n hn).map (groups R (n + 1))) := by
  have he := upperOriginal_groups_eventual_image R X n (n + 1) le_rfl h
  have hc : ProGroup.IsEventuallyImageSurjective
      (((left R X n hn).map (groups R (n + 1))).comp
        ((right R X n hn).map (groups R (n + 1)))) := by
    rw [groups_fac]
    exact he
  exact ProGroup.proIso_of_injective_and_eventual_image _ (right_groups_injective_succ R X n hn)
    (ProGroup.imageSurjective_right_of_comp _ _ hc)

lemma right_groups_proIso_high (j : ℤ) (hj : n + 1 < j) :
    IsProIso ((right R X n hn).map (groups R j)) := by
  apply ProGroup.proIso_of_cofinal_bijective
  intro i
  have := middle_groups_subsingleton R X n hn j hj i
  have := upperTarget_groups_subsingleton R X n j hj i
  exact ⟨i, le_refl i, Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
