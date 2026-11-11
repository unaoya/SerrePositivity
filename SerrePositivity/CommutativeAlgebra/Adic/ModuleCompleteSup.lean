module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-!
# 二つのイデアルの和に沿う加群の完備性

## 概要
I 進完備な加群について、I 冪商がすべて J 進完備なら、加群は I + J 進完備。

## 方針
和の冪と二つの冪の和の共終性を使い、各 I 冪商の極限を持ち上げる。

## 規約
任意の可換環上の古典的なイデアル進完備性。

## 使われ方
BS 著者版 Lemma 3.7 (2) の古典的完備性。
-/

public section

namespace SerrePositivity

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem smodEq_quotient_smul_iff (U : Submodule R M) (J : Ideal R)
    (n : ℕ) (x y : M) :
    U.mkQ x ≡ U.mkQ y [SMOD (J ^ n • (⊤ : Submodule R (M ⧸ U)))] ↔
      x ≡ y [SMOD (U ⊔ J ^ n • (⊤ : Submodule R M))] := by
  have hm : Submodule.map U.mkQ (J ^ n • (⊤ : Submodule R M)) =
      J ^ n • (⊤ : Submodule R (M ⧸ U)) := by
    rw [Submodule.map_smul'', Submodule.map_top, U.range_mkQ]
  have he : (J ^ n • (⊤ : Submodule R (M ⧸ U))).comap U.mkQ =
      U ⊔ J ^ n • (⊤ : Submodule R M) := by
    rw [← hm, Submodule.comap_map_mkQ]
  simp only [SModEq.sub_mem, ← map_sub, ← Submodule.mem_comap, he]

/-- 概要：I 進完備で各 I 冪商が J 進完備な加群は I + J 進完備。
方針：和の冪の合同を二つの冪の合同と比較する。
規約：完備性は分離性と前完備性。
使われ方：主生成元と p による二元完備性（BS 著者版 Lemma 3.7 (2)）。 -/
theorem isAdicComplete_module_sup_of_complete_quotients (I J : Ideal R)
    [IsAdicComplete I M] [∀ n : ℕ, IsAdicComplete J (M ⧸ (I ^ n • ⊤ : Submodule R M))] :
    IsAdicComplete (I ⊔ J) M := by
  classical
  let U (n : ℕ) := I ^ n • (⊤ : Submodule R M)
  have hle (n k : ℕ) :
      (I ⊔ J) ^ (n + k) • (⊤ : Submodule R M) ≤ U n ⊔ J ^ k • ⊤ := by
    change (I ⊔ J) ^ (n + k) • (⊤ : Submodule R M) ≤ I ^ n • ⊤ ⊔ J ^ k • ⊤
    rw [← Submodule.sup_smul]
    exact Submodule.smul_mono_left Ideal.sup_pow_add_le_pow_sup_pow
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff I M) x
    intro n
    have hzero : (U n).mkQ x = 0 := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro k
      apply (smodEq_quotient_smul_iff (U n) J k x 0).mpr
      have hh := hx (n + k)
      exact hh.mono (hle n _)
    exact SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hzero)
  · intro f hf
    have hlim (n : ℕ) : ∃ L : M ⧸ U n, ∀ k : ℕ,
        (U n).mkQ (f (n + k)) ≡ L [SMOD (J ^ k • (⊤ : Submodule R (M ⧸ U n)))] := by
      apply IsPrecomplete.prec' (I := J)
      intro a b hab
      apply (smodEq_quotient_smul_iff (U n) J a _ _).mpr
      have hh := hf (Nat.add_le_add_left hab n)
      exact hh.mono (hle n _)
    choose L hL using hlim
    choose r hr using (fun n ↦ (U n).mkQ_surjective (L n))
    have ha (n k : ℕ) : f (n + k) ≡ r n [SMOD (U n ⊔ J ^ k • ⊤)] := by
      apply (smodEq_quotient_smul_iff (U n) J k _ _).mp
      rw [hr]
      exact hL n k
    have hc : ∀ {n m : ℕ}, n ≤ m → r n ≡ r m [SMOD (U n)] := by
      intro n m hnm
      have hq : (U n).mkQ (r n) = (U n).mkQ (r m) := by
        apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
        intro k
        apply (smodEq_quotient_smul_iff (U n) J k _ _).mpr
        have h1 := (ha n (m + k)).mono
          (sup_le_sup_left (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left k m))) _)
        have h2 := (ha m (n + k)).mono
          (sup_le_sup (Submodule.smul_mono_left (Ideal.pow_le_pow_right hnm))
            (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_left k n))))
        rw [show m + (n + k) = n + (m + k) by omega] at h2
        exact h1.symm.trans h2
      exact SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp hq)
    obtain ⟨a, ha'⟩ := IsPrecomplete.prec' (I := I) r hc
    refine ⟨a, ?_⟩
    intro n
    have h1 := hf (show n ≤ n + n by omega)
    have h2 := (ha n n).mono
      (sup_le
        (Submodule.smul_mono_left (pow_le_pow_left' le_sup_left n))
        (Submodule.smul_mono_left (pow_le_pow_left' le_sup_right n)))
    have h3 : r n ≡ a [SMOD ((I ⊔ J) ^ n • ⊤ : Submodule R M)] := (ha' n).mono
      (Submodule.smul_mono_left (pow_le_pow_left' (show I ≤ I ⊔ J from le_sup_left) n))
    exact h1.trans (h2.trans h3)

end SerrePositivity
