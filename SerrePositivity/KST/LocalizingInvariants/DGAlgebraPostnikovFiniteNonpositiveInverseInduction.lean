module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteNonpositiveInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroNonpositiveInverseRoof

/-!
概要：有限範囲の元のホモロジー pro 同型から、有限切断の実両三角形付き逆を構成する。
方針：零段から帰納し、次段の右逆と同じ次数の対角右逆を組み合わせる。
規約：下段逆・対角比較・左経路を追加入力にしない。
使われ方：有限切断の pro 比較と、bounded-below な射の切断判定。
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
variable (R : Type u) [CommRing R]

lemma postnikovFiniteMap_exists_nonpositiveInverseRoof (cutoff : ℕ) :
    ∀ {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
      (h : ∀ j : ℤ, 0 ≤ j → j ≤ (cutoff : ℤ) →
        IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) (i : ℕ),
      ∃ m, ∃ hi : i ≤ m,
        Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R cutoff)) i m hi) := by
  induction cutoff with
  | zero =>
      intro A B f h i
      exact postnikovZeroMap_exists_nonpositiveInverseRoof R f (h 0 (by omega) (by omega)) i
  | succ n ih =>
      intro A B f h i
      have hn : 0 ≤ (n : ℤ) := by omega
      have h₀ := h 0 (by omega) (by omega)
      have hnext := h ((n : ℤ) + 1) (by omega) (by omega)
      have lower (j : ℕ) := ih f (fun z hz hzn => h z hz (by omega)) j
      let delta := postnikovFiniteNonpositiveDiagonal R ((n : ℤ) + 1) f
      have hdelta (z : ℤ) (hz : 0 ≤ z) (hzn : z ≤ (n : ℤ) + 1) :
          IsProIso ((delta.map (nonpositiveInclusion R)).map (groups R z)) :=
        postnikovFiniteNonpositiveDiagonal_groups_proIso R ((n : ℤ) + 1) f
          (fun z hz hzn => h z hz (by omega)) z hz hzn
      have lowerDelta (j : ℕ) := ih delta
        (fun z hz hzn => hdelta z hz (by omega)) j
      obtain ⟨m, him, ⟨qcut⟩⟩ := exists_postnikovSuccessorNativeRightInverseRoof R hn delta
        (hdelta 0 (by omega) (by omega))
        (hdelta ((n : ℤ) + 1) (by omega) le_rfl) lowerDelta i
      have hsource : ((postnikovFiniteDiagonalSource R ((n : ℤ) + 1)
          (A := A)).obj i).obj.X.IsGE (-((n : ℤ) + 1)) := by
        change (postnikov R (A.obj i).obj ((n : ℤ) + 1)).X.IsGE (-((n : ℤ) + 1))
        have := postnikov_lowerBound R (A.obj i).obj ((n : ℤ) + 1)
        infer_instance
      have htarget : ((postnikovFiniteDiagonalTarget R ((n : ℤ) + 1) f).obj i).obj.X.IsGE
          (-((n : ℤ) + 1)) := by
        have := postnikovFiniteDiagonalTarget_lowerBound R ((n : ℤ) + 1) f i
        infer_instance
      let q := qcut.ofPostnikovBounded R ((n : ℤ) + 1) hsource htarget
      obtain ⟨k, hmk, ⟨c⟩⟩ := exists_postnikovSuccessorNativeRightInverseRoof R hn f
        h₀ hnext lower m
      have result := postnikovFiniteInverseRoofOfDiagonalRight R ((n : ℤ) + 1) f q c
      refine ⟨k, him.trans hmk, ?_⟩
      have hcast : (n.succ : ℤ) = (n : ℤ) + 1 := by omega
      rw [hcast]
      exact ⟨result⟩

lemma postnikovFiniteMap_exists_nonpositiveInverseRoof_int (cutoff : ℤ) (hc : 0 ≤ cutoff)
    {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R cutoff)) i m hi) := by
  have hcast : (cutoff.toNat : ℤ) = cutoff := Int.toNat_of_nonneg hc
  have result := postnikovFiniteMap_exists_nonpositiveInverseRoof R cutoff.toNat f
    (fun j hj hjn => h j hj (by omega)) i
  rw [hcast] at result
  exact result

lemma exists_postnikovFiniteSuccessorNativeRightInverseRoof {cutoff : ℤ} (hc : 0 ≤ cutoff)
    {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
    (h : ∀ j : ℤ, 0 ≤ j → j ≤ cutoff + 1 →
      IsProIso ((f.map (nonpositiveInclusion R)).map (groups R j))) (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m,
      Nonempty (NativeRightInverseRoof R (f.map (postnikovFunctor R (cutoff + 1))) i m hi) := by
  apply exists_postnikovSuccessorNativeRightInverseRoof R hc f
    (h 0 (by omega) (by omega)) (h (cutoff + 1) (by omega) le_rfl)
  intro j
  exact postnikovFiniteMap_exists_nonpositiveInverseRoof_int R cutoff hc f
    (fun z hz hzn => h z hz (by omega)) j

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
