module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Faces
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.IntervalExtrema

/-!
模型。文献の定義との比較は後で
# 同色の異なる区間の高さが厳密に離れるときの面の単射性

Berger–Fresse §2.2.6、M14 L12a のC453の法則。
同じ区間では元の二座標を、異なる区間では元の両端を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 同色の区間が高さで厳密に離れれば、元の面は単射（BF §2.2.6）。 -/
lemma vertices_injective_of_strict_intervals {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (a : Fin r)
    (h : ∀ p p', v.val p = a → v.val p' = a → p < p' → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.hi s p < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo s p') :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertices s v a) := by
  intro i j hij
  let E := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v.val a).orderEmbOfFin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s v a)
  have hi := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v.val a).orderEmbOfFin_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s v a) i
  have hj := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v.val a).orderEmbOfFin_mem (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions_card_eq s v a) j
  have hp : v.val (s.horizontal (E i)) = a := (Finset.mem_filter.mp hi).2
  have hp' : v.val (s.horizontal (E j)) = a := (Finset.mem_filter.mp hj).2
  have hv : s.vertical (E i) = s.vertical (E j) := hij
  rcases lt_trichotomy (s.horizontal (E i)) (s.horizontal (E j)) with hlt | he | hgt
  · have hb := h _ _ hp hp' hlt
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s _ (E i) rfl
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s _ (E j) rfl
    have heq := congrArg Fin.val hv
    omega
  · exact E.injective (s.vertex_injective (Prod.ext he hv))
  · have hb := h _ _ hp' hp hgt
    have hl := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vertical_le_hi s _ (E j) rfl
    have hr := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.lo_le_vertical s _ (E i) rfl
    have heq := congrArg Fin.val hv
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
