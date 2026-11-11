module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExPairingCore

/-!
# 型 II の面での複雑度の減少

概要：対応先の同次元の型 II の面では、元と異なる限り複雑度が厳しく減る。
方針：前側の面の閾値の減少を使い、後ろの面は型 I または退化として除く。
規約：Moss 2020 Theorem 22 の正則性の証明。
使われ方：最小複雑度を Mathlib の WeakRankFunction とする。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：複雑度の上界を満たす拡張は型 II に属さない。
方針：最小閾値に一致すれば前段の像となり、より大きければ退化する。
規約：Moss 2020 Theorem 22 の正則性、後ろの面を除く補助。
使われ方：後ろの面が同次元の型 II の先行元とならないこと。
-/
theorem exExpansion_notMem_typeTwo (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exComplexity X ⦋n⦌ k) :
    exExpansion X n k s ∉ exTypeTwo X (n + 1) := by
  intro ht
  have hl := (exComplexityLevel_le_iff X ⦋n⦌ s k).mpr hs
  rcases lt_or_eq_of_le hl with hlt | heq
  · exact ((SSet.ex.obj X).mem_nonDegenerate_iff_notMem_degenerate _).mp ht.1
      (exExpansion_degenerate_of_complexity_lt X n _ k hlt s (exComplexityLevel_mem X _ s))
  · apply ht.2.2
    refine ⟨s, ?_⟩
    change exExpansion X n (exComplexityLevel X ⦋n⦌ s) s = _
    rw [heq]

/--
概要：正次元の型 II の異なる単体が対応先の面なら、その複雑度は厳しく小さい。
方針：指定面の前後で場合分けし、後ろは拡張が型 II でないことと矛盾させる。
規約：Moss 2020 Theorem 22 の同次元の先行関係の rank の減少。
使われ方：弱 rank 関数の構成。
-/
theorem exPairingStep_face_rank_lt_succ (X : SSet.{u}) (n : ℕ)
    (s t : (SSet.ex.obj X) _⦋n + 1⦌) (hs : s ∈ exTypeTwo X (n + 1))
    (ht : t ∈ exTypeTwo X (n + 1)) (hst : s ≠ t) (i : Fin (n + 3))
    (hi : (SSet.ex.obj X).δ i (exPairingStep X (n + 1) t) = s) :
    (exComplexityLevel X ⦋n + 1⦌ s).val < (exComplexityLevel X ⦋n + 1⦌ t).val := by
  let k := exComplexityLevel X ⦋n + 1⦌ t
  change (SSet.ex.obj X).δ i (exExpansion X (n + 1) k t) = s at hi
  have hk : k ≠ 0 := fun h => ht.2.1 ((exComplexityLevel_zero_iff X _ t).mp h)
  by_cases hie : i = k.succ
  · subst i
    rw [exExpansion_face] at hi
    exact (hst hi.symm).elim
  rcases lt_or_gt_of_ne hie with hlt | hgt
  · let h := k.pred hk
    have he : h.succ = k := Fin.succ_pred k hk
    have hi' : i ≤ h.succ.castSucc := by
      rw [he]
      change i.val ≤ k.val
      have hv : i.val < k.val + 1 := hlt
      omega
    have hm : t ∈ exComplexity X ⦋n + 1⦌ h.succ := he.symm ▸ exComplexityLevel_mem X _ t
    have hr := exExpansion_front_complexity X n h i hi' t hm
    rw [he, hi] at hr
    have hl := (exComplexityLevel_le_iff X ⦋n + 1⦌ s h.castSucc).mpr hr
    have hval : h.val + 1 = k.val := congrArg Fin.val he
    have hbound : (exComplexityLevel X ⦋n + 1⦌ s).val ≤ h.val := hl
    change (exComplexityLevel X ⦋n + 1⦌ s).val < k.val
    omega
  · have hkl : k ≠ Fin.last (n + 1) := by
      intro he
      have hv := i.isLt
      have hg : k.val + 1 < i.val := hgt
      simp only [he, Fin.val_last] at hg
      omega
    let l := k.castPred hkl
    have hl : l.castSucc = k := Fin.castSucc_castPred k hkl
    have hiz : i ≠ 0 := ne_of_gt ((Fin.zero_le k.succ).trans_lt hgt)
    let j := i.pred hiz
    have hj : j.succ = i := Fin.succ_pred i hiz
    have hkj : l.castSucc < j := by
      rw [hl]
      change k.val < i.val - 1
      have hg : k.val + 1 < i.val := hgt
      omega
    have hm : t ∈ exComplexity X ⦋n + 1⦌ l.castSucc := hl.symm ▸ exComplexityLevel_mem X _ t
    have hf := exComplexity_face X n l j t hm
    have he : exExpansion X n l ((SSet.ex.obj X).δ j t) = s := by
      rw [← exExpansion_rear_face X n l j hkj t]
      simpa only [hl, hj] using hi
    exact (exExpansion_notMem_typeTwo X n l _ hf (he.symm ▸ hs)).elim

/--
概要：同次元の異なる型 II の単体が対応先の面なら最小複雑度が厳しく減る。
方針：正次元の減少の補題と、零次元の型 II の不存在を使う。
規約：Moss 2020 Theorem 22 の正則性の rank の減少。
使われ方：全次元の弱 rank 関数。
-/
theorem exPairingStep_face_rank_lt (X : SSet.{u}) (n : ℕ)
    (s t : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exTypeTwo X n)
    (ht : t ∈ exTypeTwo X n) (hst : s ≠ t) (i : Fin (n + 2))
    (hi : (SSet.ex.obj X).δ i (exPairingStep X n t) = s) :
    (exComplexityLevel X ⦋n⦌ s).val < (exComplexityLevel X ⦋n⦌ t).val := by
  cases n with
  | zero =>
      have hz : exComplexityLevel X ⦋0⦌ s = 0 := by
        apply Fin.ext
        have h := (exComplexityLevel X ⦋0⦌ s).isLt
        change (exComplexityLevel X ⦋0⦌ s).val = 0
        change (exComplexityLevel X ⦋0⦌ s).val < 1 at h
        omega
      exact (hs.2.1 ((exComplexityLevel_zero_iff X _ s).mp hz)).elim
  | succ n => exact exPairingStep_face_rank_lt_succ X n s t hs ht hst i hi

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
