module

public import SerrePositivity.EInfinity.SimplexCuts.Faces
public import SerrePositivity.EInfinity.SimplexCuts.IntervalExtrema

/-!
# 同色の異なる区間の高さが厳密に離れるときの面の単射性

Berger–Fresse §2.2.6、M14 L12a のC453の法則。
同じ区間では元の二座標を、異なる区間では元の両端を比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 同色の区間が高さで厳密に離れれば、元の面は単射（BF §2.2.6）。 -/
lemma vertices_injective_of_strict_intervals {m q r : ℕ} (s : Cut m q)
    (v : Surjection.Word r (m + 1)) (a : Fin r)
    (h : ∀ p p', v.val p = a → v.val p' = a → p < p' → hi s p < lo s p') :
    Function.Injective (vertices s v a) := by
  intro i j hij
  let E := (colorPositions s v.val a).orderEmbOfFin (colorPositions_card_eq s v a)
  have hi := (colorPositions s v.val a).orderEmbOfFin_mem (colorPositions_card_eq s v a) i
  have hj := (colorPositions s v.val a).orderEmbOfFin_mem (colorPositions_card_eq s v a) j
  have hp : v.val (s.horizontal (E i)) = a := (Finset.mem_filter.mp hi).2
  have hp' : v.val (s.horizontal (E j)) = a := (Finset.mem_filter.mp hj).2
  have hv : s.vertical (E i) = s.vertical (E j) := hij
  rcases lt_trichotomy (s.horizontal (E i)) (s.horizontal (E j)) with hlt | he | hgt
  · have hb := h _ _ hp hp' hlt
    have hl := vertical_le_hi s _ (E i) rfl
    have hr := lo_le_vertical s _ (E j) rfl
    have heq := congrArg Fin.val hv
    omega
  · exact E.injective (s.vertex_injective (Prod.ext he hv))
  · have hb := h _ _ hp' hp hgt
    have hl := vertical_le_hi s _ (E j) rfl
    have hr := lo_le_vertical s _ (E i) rfl
    have heq := congrArg Fin.val hv
    omega

end SerrePositivity.EInfinity.SimplexCuts
