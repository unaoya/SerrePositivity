module

public import SerrePositivity.EInfinity.SimplexCuts.RemainingColorFaces
public import SerrePositivity.EInfinity.SimplexCuts.InsertedColorFaces
public import SerrePositivity.EInfinity.SimplexCuts.CompositeFaceFamilies

/-!
# 元の合成切断と二段切断の指定面の全族の一致

Berger–Fresse §2.2.6、M14 L12a のC451。
元の入力分解で残り色と挿入色を読み、出力次数と指定面をそのまま照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C451：元の全出力次数と指定面の族は二段切断と厳密に一致（BF §2.2.6）。 -/
lemma positiveCompositeFaceFamily_eq_nested {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveCompositeCutIndex u v k q) :
    positiveCompositeFaceFamily u v k c =
      positiveNestedFaceFamily u v k (positiveCompositeNestedMap u v k c) := by
  funext a
  obtain ⟨s, hs⟩ := (operadInsertionEquiv m (n + 1) k).symm.surjective a
  rw [← hs]
  cases s with
  | inl b =>
    simpa only [positiveCompositeFaceFamily, positiveNestedFaceFamily, positiveCompositeNestedMap,
      IntervalCuts.insertionFamily, BarrattEccles.remainingPosition, Equiv.apply_symm_apply]
      using (positiveComposite_remaining_face u v k c b).symm
  | inr b =>
    simpa only [positiveCompositeFaceFamily, positiveNestedFaceFamily, positiveCompositeNestedMap,
      IntervalCuts.insertionFamily, BarrattEccles.insertedPosition, Equiv.apply_symm_apply]
      using positiveComposite_inserted_face u v k c b

end SerrePositivity.EInfinity.SimplexCuts
