module

public import SerrePositivity.KST.Comparison.RingHornLower

/-!
# ホーンの高い面からの補正と充填の存在

概要：欠けた面より後の面を逆順に合わせ、低い面を保持して全ホーンを充填する。
方針：退化による一段の補正と自然数の逆向きの有限帰納を使う。
規約：KST Lemma 2.13 の加法群の Kan 性の構成の後半。
使われ方：単体的環の台集合の Kan 性の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite
open scoped Simplicial

/--
概要：高い面を一つ合わせても、低い面とそれより高い面は保持される。
方針：面と退化の交換恒等式で、互換性が与える零の誤差を使う。
規約：欠けた面より後の指定面を補正する。
使われ方：高い面の逆向きの有限帰納の一段。
-/
theorem RingHornFaces.correct_upper_step (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) (y : A.obj (op ⦋n + 2⦌))
    (i : Fin (n + 2)) (hki : k < i.succ) (hi : i.succ ≠ k)
    (hy : ∀ (j : Fin (n + 3)) (hj : j ≠ k), j < k ∨ i.succ < j →
      (A.δ j).hom y = F.face j hj) :
    ∀ (j : Fin (n + 3)) (hj : j ≠ k), j < k ∨ i.succ ≤ j →
      (A.δ j).hom (ringAddDegeneracy A y i
        (F.face i.succ hi - (A.δ i.succ).hom y)) = F.face j hj := by
  intro j hj hji
  by_cases h : j = i.succ
  · subst j
    exact ringAddDegeneracy_correct_upper A y i _
  · rcases hji with hlow | hhigh
    · have hlt : j < i.castSucc := by
        change j.val < i.val
        change j.val < k.val at hlow
        change k.val < i.val + 1 at hki
        omega
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        simp at hlt
      obtain ⟨p, rfl⟩ := i.eq_succ_of_ne_zero hi0
      obtain ⟨q, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hlt)
      have hqp : q ≤ p.castSucc := by
        change q.val ≤ p.val
        change q.val < p.val + 1 at hlt
        omega
      have hqi : q ≤ p.succ := by
        change q.val ≤ p.val + 1
        exact Nat.le_trans (Fin.le_iff_val_le_val.mp hqp) (Nat.le_succ _)
      have he := F.error_face_low A y q p.succ hqi hj hi
        (hy q.castSucc hj (Or.inl hlow))
      exact (ringAddDegeneracy_preserves_low A y p q hqp _ he).trans
        (hy q.castSucc hj (Or.inl hlow))
    · have hlt : i.succ < j := lt_of_le_of_ne hhigh (Ne.symm h)
      have hiLast : i ≠ Fin.last (n + 1) := by
        intro hiLast
        subst i
        have hjb := j.isLt
        change n + 2 < j.val at hlt
        omega
      obtain ⟨p, rfl⟩ := i.eq_castSucc_of_ne_last hiLast
      obtain ⟨q, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hlt)
      have hpq : p.castSucc < q := by
        change p.val < q.val
        change p.val + 1 < q.val + 1 at hlt
        omega
      have hpsq : p.succ ≤ q := by
        change p.val + 1 ≤ q.val
        exact hpq
      have ht : p.succ.castSucc ≠ k := by simpa only [Fin.castSucc_succ] using hi
      have he : (A.δ q).hom
          (F.face p.castSucc.succ hi - (A.δ p.castSucc.succ).hom y) = 0 := by
        simpa only [Fin.castSucc_succ] using
          F.error_face_high A y p.succ q hpsq ht hj (hy q.succ hj (Or.inr hlt))
      exact (ringAddDegeneracy_preserves_high A y p q hpq _ he).trans
        (hy q.succ hj (Or.inr hlt))

/--
概要：単体的環の次元二以上の互換なホーンは充填できる。
方針：欠けた面より前を順に合わせた後、それより後を逆順に合わせる。
規約：全ての指定面に厳密に一致し、欠けた面の指定値は要求しない。
使われ方：Kan 性の正の次数のホーンの充填。
-/
theorem RingHornFaces.exists_filler (A : SimplicialObject RingCat.{u}) {n : ℕ}
    {k : Fin (n + 3)} (F : RingHornFaces A n k) :
    ∃ y : A.obj (op ⦋n + 2⦌), ∀ (j : Fin (n + 3)) (hj : j ≠ k),
      (A.δ j).hom y = F.face j hj := by
  let P (m : ℕ) : Prop := ∃ y : A.obj (op ⦋n + 2⦌),
    ∀ (j : Fin (n + 3)) (hj : j ≠ k), j.val < k.val ∨ m < j.val →
      (A.δ j).hom y = F.face j hj
  have htop : P (n + 2) := by
    obtain ⟨y, hy⟩ := F.exists_lower_prefix A k.val (Nat.le_refl _)
    refine ⟨y, fun j hj h => ?_⟩
    rcases h with h | h
    · exact hy j hj h
    · have hjb := j.isLt
      omega
  have hstep (m : ℕ) (hm : m < n + 2) (hkm : k.val ≤ m) : P (m + 1) → P m := by
    rintro ⟨y, hy⟩
    let i : Fin (n + 2) := ⟨m, hm⟩
    have hki : k < i.succ := by
      change k.val < m + 1
      omega
    have hi : i.succ ≠ k := ne_of_gt hki
    refine ⟨ringAddDegeneracy A y i (F.face i.succ hi - (A.δ i.succ).hom y), ?_⟩
    intro j hj h
    apply F.correct_upper_step A y i hki hi (fun l hl hlt => hy l hl hlt) j hj
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hk : k.val ≤ n + 2 := by omega
  have hPk : P k.val := Nat.decreasingInduction' (P := P) hstep hk htop
  obtain ⟨y, hy⟩ := hPk
  refine ⟨y, fun j hj => hy j hj ?_⟩
  have hne : j.val ≠ k.val := fun he => hj (Fin.ext he)
  omega

end SerrePositivity.KST.Comparison
