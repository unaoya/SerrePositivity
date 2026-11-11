module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProConeComparison

/-!
概要：正次数の Tor 群模型の pro 消滅から、元の離散標的への dg 比較射の値を判定する。
方針：同じ塔の全遷移に自然なホモロジー比較と、零次数・負次数の照合を使う。
規約：Tor 模型の同定や零次数同型を証明済みとはせず、実比較として明示する。
使われ方：K-8 e の具体的 Tor 供給を受ける抽象連結度判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision

private lemma proIso_of_proZero_groups {U V : Tower CommGrpCat.{u}} (f : LevelHom U V)
    (hU : IsProZero U) (hV : IsProZero V) : IsProIso f := by
  intro i
  obtain ⟨m, hm, hzU⟩ := hU i
  obtain ⟨n, hn, hzV⟩ := hV i
  refine ⟨max m n, hm.trans (le_max_left _ _), 0, ?_, ?_⟩
  · rw [Limits.comp_zero, ← U.transition_comp (le_max_left _ _) hm, hzU, Limits.comp_zero]
  · rw [Limits.zero_comp, ← V.transition_comp (le_max_right _ _) hn, hzV, Limits.comp_zero]

private lemma proZero_of_subsingleton_groups (U : Tower CommGrpCat.{u})
    (hU : ∀ i, Subsingleton (U.obj i)) : IsProZero U := by
  intro i
  refine ⟨i, le_rfl, ?_⟩
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact (hU i).elim _ _

variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

/-- 零次数を保つ離散標的への射は、正次数の源の pro 消滅から全次数の pro 同型になる。 -/
lemma piProEquivalence_of_positive_proZero
    (hB : ∀ i, (B.obj i).obj.X.IsGE 0)
    (hzero : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hpos : ∀ j : ℤ, 0 < j →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsPiProEquivalence R (f.map (nonpositiveInclusion R)) := by
  intro j
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · have hA : ∀ i, Subsingleton
        (((A.map (nonpositiveInclusion R)).map (groups R j)).obj i) := by
      intro i
      have : (A.obj i).obj.X.IsStrictlyLE 0 := (A.obj i).property
      exact groups_subsingleton_of_homology_zero R _ j
        ((A.obj i).obj.X.isZero_of_isLE 0 (-j) (by omega))
    have hB' : ∀ i, Subsingleton
        (((B.map (nonpositiveInclusion R)).map (groups R j)).obj i) := by
      intro i
      have : (B.obj i).obj.X.IsStrictlyLE 0 := (B.obj i).property
      exact groups_subsingleton_of_homology_zero R _ j
        ((B.obj i).obj.X.isZero_of_isLE 0 (-j) (by omega))
    exact proIso_of_proZero_groups _ (proZero_of_subsingleton_groups _ hA)
      (proZero_of_subsingleton_groups _ hB')
  · exact hzero
  · apply proIso_of_proZero_groups _ (hpos j hj)
    apply proZero_of_subsingleton_groups
    intro i
    have := hB i
    exact groups_subsingleton_of_homology_zero R _ j
      ((B.obj i).obj.X.isZero_of_isGE 0 (-j) (by omega))

/-- 正次数の実 Tor 群の塔との自然な比較を使い、元の射の pro 同型を判定する。
比較は各対象の群同型だけでなく、元の全遷移を保つレベル射として入力する。 -/
lemma piProEquivalence_of_positiveTorModel
    (hB : ∀ i, (B.obj i).obj.X.IsGE 0)
    (hzero : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (T : ℕ → Tower CommGrpCat.{u})
    (e : ∀ j : ℕ, 0 < j →
      LevelHom (T j) ((A.map (nonpositiveInclusion R)).map (groups R j)))
    (he : ∀ j hj i, IsIso ((e j hj).app i))
    (hTor : ∀ j : ℕ, 0 < j → IsProZero (T j)) :
    IsPiProEquivalence R (f.map (nonpositiveInclusion R)) := by
  apply piProEquivalence_of_positive_proZero R f hB hzero
  intro j hj
  lift j to ℕ using hj.le with n hn
  have hnpos : 0 < n := by omega
  have : ∀ i, IsIso ((e n hnpos).app i) := he n hnpos
  exact IsProZero.of_levelwiseIso (e n hnpos) (hTor n hnpos)

variable (Φ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u + 1} ⟶ Sp.{u + 1}) {k : ℤ} (hΦ : IsKConnective R Φ k)
include hΦ

/-- 同じ元の dg 比較射の値に、正次数 Tor の pro 消滅の抽象判定を適用する。 -/
lemma IsKConnective.invariantLevelMap_piProEquivalence_of_positiveTorModel
    (hB : ∀ i, (B.obj i).obj.X.IsGE 0)
    (hzero : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (T : ℕ → Tower CommGrpCat.{u})
    (e : ∀ j : ℕ, 0 < j →
      LevelHom (T j) ((A.map (nonpositiveInclusion R)).map (groups R j)))
    (he : ∀ j hj i, IsIso ((e j hj).app i))
    (hTor : ∀ j : ℕ, 0 < j → IsProZero (T j)) :
    ProSpectrum.IsPiProEquivalence
      (invariantLevelMap R Φ (f.map (nonpositiveInclusion R))) :=
  hΦ.invariantLevelMap_piProEquivalence_of_piProEquivalence R f Φ
    (piProEquivalence_of_positiveTorModel R f hB hzero T e he hTor)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
