module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ComponentExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.IntervalVertices
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionCursorHead

/-!
模型。文献の定義との比較は後で
# 元の分割成分の実際の垂直合成ブロックへの転送

概要：Berger–Fresse §1.5.7 の内側分割成分を元の外側指定出現の行で合成して抽出する。
方針：元の外側進行状態の先頭条件と、元の内側成分の置換付き証跡を使う。
規約：元の二つの成功と任意の後続成功だけを入力とする。
使われ方：候補経路の垂直成分の全行を実際の合成表へまとめて移す。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の内側分割成分を実際の固定外側合成行列で抽出（BF §1.5.7）。
方針：元の指定出現で進めた外側行に、元の内側成分証跡の全行を転送する。
規約：行表示や成分成功を別途仮定しない。後続抽出は任意。
使われ方：合成経路の一つの垂直成分を実際に構成して後続へつなぐ。 -/
lemma componentVerticalExtraction_success {m n d e t : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + 1) d)
    (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (m + 1) d)
    (hu : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w s) [] = some (List.ofFn u.val))
    (p : Fin (m + 1 + d)) (k : Fin (m + 1)) (hk : u.val p = k)
    (z : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n e) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n e)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows z r) [] = some (List.ofFn v.val))
    (cuts : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OverlapPartition t (n + e)) (hl : 0 < n + e) (i : Fin t)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu p)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv (cuts.endPosition hl i))) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s u.val hu p)) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction z r v hv cuts hl i).weightedVertices ++ rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu p)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv (cuts.startPosition hl i))) =
      some ((cuts.segment v.val i).map (insertedPosition m n k) ++ tail) := by
  obtain ⟨post, houter⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved_available_slot w s u.val hu p k hk
  have hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction z r v hv cuts hl i).weightedVertices)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv (cuts.startPosition hl i))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction z r v hv cuts hl i).selected
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved z r v.val hv (cuts.endPosition hl i)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReductionInterval.permutationRows_eq]
    exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction z r v hv cuts hl i).trace
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalExtraction_success (w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRow w s u.val hu p)) k
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reductionRemoved w s u.val hu p) post houter _ _ _ _ hinner rest tail ht
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.componentExtraction_word] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
