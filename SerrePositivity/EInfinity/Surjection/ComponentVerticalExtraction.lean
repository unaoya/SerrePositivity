module

public import SerrePositivity.EInfinity.Surjection.ComponentExtraction
public import SerrePositivity.EInfinity.Surjection.VerticalExtraction
public import SerrePositivity.EInfinity.TableReduction.IntervalVertices
public import SerrePositivity.EInfinity.TableReduction.ReductionCursorHead

/-!
# 元の分割成分の実際の垂直合成ブロックへの転送

概要：Berger–Fresse §1.5.7 の内側分割成分を元の外側指定出現の行で合成して抽出する。
方針：元の外側進行状態の先頭条件と、元の内側成分の置換付き証跡を使う。
規約：元の二つの成功と任意の後続成功だけを入力とする。
使われ方：候補経路の垂直成分の全行を実際の合成表へまとめて移す。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：元の内側分割成分を実際の固定外側合成行列で抽出（BF §1.5.7）。
方針：元の指定出現で進めた外側行に、元の内側成分証跡の全行を転送する。
規約：行表示や成分成功を別途仮定しない。後続抽出は任意。
使われ方：合成経路の一つの垂直成分を実際に構成して後続へつなぐ。 -/
lemma componentVerticalExtraction_success {m n d e t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (s : Schedule (m + 1) d)
    (u : BasisWord (m + 1) d)
    (hu : reduceRows (rows w s) [] = some (List.ofFn u.val))
    (p : Fin (m + 1 + d)) (k : Fin (m + 1)) (hk : u.val p = k)
    (z : Fin (e + 1) → Equiv.Perm (Fin n)) (r : Schedule n e) (v : BasisWord n e)
    (hv : reduceRows (rows z r) [] = some (List.ofFn v.val))
    (cuts : OverlapPartition t (n + e)) (hl : 0 < n + e) (i : Fin t)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (compositionStateRemoved k (reductionRemoved w s u.val hu p)
      (reductionRemoved z r v.val hv (cuts.endPosition hl i))) = some tail) :
    reduceRows
      (fixedOuterRows (w (reductionRow w s u.val hu p)) k
        (componentExtraction z r v hv cuts hl i).weightedVertices ++ rest)
      (compositionStateRemoved k (reductionRemoved w s u.val hu p)
        (reductionRemoved z r v.val hv (cuts.startPosition hl i))) =
      some ((cuts.segment v.val i).map (insertedPosition m n k) ++ tail) := by
  obtain ⟨post, houter⟩ := reductionRemoved_available_slot w s u.val hu p k hk
  have hinner : ExtractionPrefix
      (permutationRows (componentExtraction z r v hv cuts hl i).weightedVertices)
      (reductionRemoved z r v.val hv (cuts.startPosition hl i))
      (componentExtraction z r v hv cuts hl i).selected
      (reductionRemoved z r v.val hv (cuts.endPosition hl i)) := by
    rw [ReductionInterval.permutationRows_eq]
    exact (componentExtraction z r v hv cuts hl i).trace
  have hs := verticalExtraction_success (w (reductionRow w s u.val hu p)) k
    (reductionRemoved w s u.val hu p) post houter _ _ _ _ hinner rest tail ht
  simpa only [componentExtraction_word] using hs

end SerrePositivity.EInfinity.Surjection
