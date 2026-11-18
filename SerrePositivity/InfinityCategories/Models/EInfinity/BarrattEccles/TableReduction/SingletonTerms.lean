module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.InsertedVertexRows

/-!
模型。文献の定義との比較は後で
# 一文字行から生じる正規化された境界項

概要：Berger–Fresse §1.4.4 の出力と符号の一致を χ の次数加群へ移す。
方針：実際の削除位置で eraseIdx を計算して listGenerator を適用する。
規約：退化した出力と削除後の退化も正規化の定義で処理する。
使われ方：一般の境界恒等式で頂点境界に残る項を次数加群上で比較する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：一文字行の符号付き削除項は対応する頂点境界の項（BF §1.4.4）。
方針：行の削除証明書から削除位置を取り、出力の削除と符号を同時に置換する。
規約：係数環は任意の可換環であり、全ての頂点位置を含む。
使われ方：table の削除和を頂点境界と残りの相殺項へ分ける。 -/
lemma singleton_deletion_term (A : Type u) [CommRing A] {n d : ℕ}
    (w : Fin (d + 2) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n (d + 1))
    (i : Fin (d + 2)) (hi : (r.val i).val = 1)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    ∃ k : Fin out.length,
      k.val = ((List.ofFn (fun j => (r.val j).val)).take i.val).sum ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (fun j : Fin out.length => out[j.val]) k •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (d := d) (out.eraseIdx k.val) =
        (-1 : ℤ) ^ i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi) := by
  obtain ⟨pre, a, post, he, hl, hc, k, hk, hcoeff⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.singleton_boundary_certificate w r i hi out h
  refine ⟨k, hk.trans hl, ?_⟩
  have hterm : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => w (i.succAbove j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleDelete r i hi) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (pre ++ post) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, hc, Option.map_some, Option.getD_some]
  have herase : out.eraseIdx pre.length = pre ++ post := by
    rw [he, List.eraseIdx_append]
    simp
  rw [hcoeff, hk, herase, hterm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
