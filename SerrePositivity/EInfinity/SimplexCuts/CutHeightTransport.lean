module

public import SerrePositivity.EInfinity.SimplexCuts.CutHeights

/-!
# 等しい次数で読む元のCutの高さの一致

Berger–Fresse §2.2.6、M14 L12a の次数移送の補助。
等しい次数の添字を合わせるだけで、元の有限切断を変えない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- C439：等しい次数の元のCutは、同じ高さなら一致する（BF §2.2.6 の移送の補助）。 -/
lemma cutHeights_heq {m q q' : ℕ} (s : Cut m q) (t : Cut m q') (h : q = q')
    (hs : ∀ i, (cutHeights s i).val = (cutHeights t i).val) : HEq s t := by
  subst q'
  apply heq_of_eq
  apply cutHeights_injective
  apply OrderHom.ext
  funext i
  exact Fin.ext (hs i)

end SerrePositivity.EInfinity.SimplexCuts
