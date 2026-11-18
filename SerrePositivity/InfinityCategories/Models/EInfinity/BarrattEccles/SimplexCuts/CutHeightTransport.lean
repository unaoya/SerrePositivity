module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutHeights

/-!
模型。文献の定義との比較は後で
# 等しい次数で読む元のCutの高さの一致

Berger–Fresse §2.2.6、M14 L12a の次数移送の補助。
等しい次数の添字を合わせるだけで、元の有限切断を変えない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- C439：等しい次数の元のCutは、同じ高さなら一致する（BF §2.2.6 の移送の補助）。 -/
lemma cutHeights_heq {m q q' : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q') (h : q = q')
    (hs : ∀ i, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights s i).val = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights t i).val) : HEq s t := by
  subst q'
  apply heq_of_eq
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutHeights_injective
  apply OrderHom.ext
  funext i
  exact Fin.ext (hs i)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
