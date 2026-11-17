module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalImageCard

/-!
概要：二点以下からの実有限単調射が底を保ち併合しなければ単射となる。
方針：異なる二点がある唯一の場合に、0と1の像が異なることを使う。
規約：空と一点の始点も含む。
使われ方：Riehl–Verity Proposition 4.2.15の先頭の実境界面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの幅の保存。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：二点以下からの実単調射が0を保ち底を併合しなければ単射。
方針：異なる二点があれば0と1であり、その像が異なることを使う。
規約：空と一点の始点を含む。使われ方：Riehl–Verity §4.2の実先頭面の幅の保存。 -/
lemma ordinalInjective_of_le_two_bottom_no_one {a b : ℕ} (f : Fin a →o Fin b)
    (ha : a ≤ 2) (h0 : ∀ i, i.val = 0 → (f i).val = 0)
    (hno : ∀ i, i.val = 1 → (f i).val ≠ 0) : Function.Injective f := by
  intro i j hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg (fun t : Fin b => t.val) hij
  by_cases hi0 : i.val = 0
  · have hfi := h0 i hi0
    by_cases hj0 : j.val = 0
    · omega
    · have hj1 : j.val = 1 := by omega
      have hfj := hno j hj1
      omega
  · by_cases hj0 : j.val = 0
    · have hfj := h0 j hj0
      have hi1 : i.val = 1 := by omega
      have hfi := hno i hi1
      omega
    · omega

end SerrePositivity.InfinityCategories.HA.Monads
