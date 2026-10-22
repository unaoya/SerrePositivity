module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovImageProGroups
public import SerrePositivity.KST.LocalizingInvariants.ProLevelArrowTower

/-!
概要：元の dg 代数の塔が次数別に (n+1)-pro-connected なら、実像分解の標的射は π-pro 同値。
方針：低次数の pro 同型、新しい層の eventual 像全射性、高次数消滅の三場合を合成する。
規約：有限 Postnikov 模型の群の判定であり、一般 pro ∞ 圏や値の同値とは主張しない。
使われ方：LT の連結なレベル表示へ接続する実図式の有限段。
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

lemma left_connected (i : ℕ) : IsConnected R ((left R X n hn).app i) (n + 1) :=
  postnikovImageFactorisationArrowSource_connected R n hn (X.obj i)

lemma middle_isConnective (i : ℕ) : IsConnective R ((middle R X n hn).obj i) :=
  postnikovImageFactorisationArrowObject_isConnective R n hn (X.obj i)

lemma right_piProEquivalence (h : IsPiProConnected R (original R X) (n + 1)) :
    IsPiProEquivalence R (right R X n hn) := by
  intro j
  by_cases hj : j ≤ n
  · exact right_groups_proIso_low R X n hn j hj
      (DGAlgebra.IsPiProConnected.groupMap_isProIso R h (by omega))
  · by_cases he : j = n + 1
    · subst j
      exact right_groups_proIso_succ R X n hn (h.2 (n + 1) le_rfl)
    · exact right_groups_proIso_high R X n hn j (by omega)

lemma factorisation_properties (h : IsPiProConnected R (original R X) (n + 1)) :
    (left R X n hn).comp (right R X n hn) = upperOriginal R X n ∧
      (∀ i, IsConnected R ((left R X n hn).app i) (n + 1)) ∧
      (∀ i, IsConnective R ((middle R X n hn).obj i)) ∧
      IsPiProEquivalence R (right R X n hn) :=
  ⟨fac R X n hn, left_connected R X n hn, middle_isConnective R X n hn,
    right_piProEquivalence R X n hn h⟩

lemma original_arrowTower {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B) :
    original R (TowerDiagram.arrowTower f) = f.map (nonpositiveInclusion R) := rfl

lemma right_piProEquivalence_of_levelHom {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
    (h : IsPiProConnected R (f.map (nonpositiveInclusion R)) (n + 1)) :
    IsPiProEquivalence R (right R (TowerDiagram.arrowTower f) n hn) :=
  right_piProEquivalence R (TowerDiagram.arrowTower f) n hn h

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovImagePro
