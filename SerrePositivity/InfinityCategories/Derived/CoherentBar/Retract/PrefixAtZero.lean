module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.PrefixSums
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateUnitCoefficients
/-!
概要：退化位置零では prefix 和の単位項だけが残り、他方のホモトピー後の和は零になる。
方針：高次退化 prefix の零性で最初の項だけを残し、切断後の次数でホモトピー列を消す。
規約：最初の単位項を消失と扱わず、対応する面との相殺のために保持する。
使われ方：正規化境界の最後の段階における面・prefix の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixRightSum_at_zero {n : ℕ} (s : I _⦋n⦌) :
    (∑ k : Fin n, dgCoherentBarPrefixRightTerm R D F s n k) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  exact dgCoherentBarHomotopy_comp_prefixColumn_zero R D F s k.val n
    (by omega) (by omega)

lemma dgCoherentBarPrefixLeftSum_at_zero {n : ℕ} (s : I _⦋n⦌) :
    (∑ k : Fin (n + 1), dgCoherentBarPrefixLeftTerm R D F s n k) =
      dgCoherentBarPrefixLeftTerm R D F s n 0 := by
  apply Finset.sum_eq_single (0 : Fin (n + 1))
  · intro k _ hne
    have hk : 1 ≤ k.val := by
      by_contra h
      apply hne
      exact Fin.ext (by change k.val = 0; omega)
    exact dgCoherentBarDegeneratePrefix_comp_block_zero R D F s
      ⟨n - n, by omega⟩ k.val (by omega) hk (by change n - n ≤ k.val; omega)
  · simp

lemma dgCoherentBarPrefixLeftTerm_at_zero_eq_face {n : ℕ} (s : I _⦋n⦌) :
    dgCoherentBarPrefixLeftTerm R D F s n 0 =
      compose R
        (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
        (y := ForgetEnrichment.to (Complex R)
          (dgCoherentBarFamily R D F (dgCoherentBarDegeneracy s 0)))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarFaceColumn R D F (I.σ 0 s) 0)
        (dgCoherentBarDegeneracyBlock R D F s 0) (show (-1 : ℤ) + 1 = 0 from rfl) := by
  have hi : (⟨n - n, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext (Nat.sub_self n)
  unfold dgCoherentBarPrefixLeftTerm
  rw [hi]
  exact congrArg (fun z => compose R
    (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, I.σ 0 s⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) z
    (dgCoherentBarDegeneracyBlock R D F s 0) (show (-1 : ℤ) + 1 = 0 from rfl))
    (dgCoherentBarPrefixColumn_first_degenerate_eq_face R D F s)

end SerrePositivity.InfinityCategories
