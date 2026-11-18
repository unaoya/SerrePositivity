module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullaryForwardSchedule
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySuccessfulLift
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleOutputUniqueness

/-!
模型。文献の定義との比較は後で
# 空語合成の成功項の有限な全射

概要：Berger–Fresse §1.5.7–9 の nullary 成功項の対応を有限型の写像へまとめる。
方針：指定値一出現で削除後も非退化な元の成功項を取り、順方向成功と逆向き存在を使う。
規約：出力 arity は正。単射性と有限和の対応は別に証明する。
使われ方：空語挿入の全成功項の全単射を構成するための順方向写像。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

/-- 概要：指定値一出現で削除後も非退化な元の成功項（BF §1.5.7–9）。
方針：既存の有限な成功 Schedule・基底語を二つの語の条件で制限する。
規約：削除による退化項と複数出現による零項を除く。
使われ方：nullary の目標成功項に対応する元の有限添字。 -/
abbrev NullarySource {m d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (k : Fin (m + 1)) :=
  {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount p.val.2.val k = 1 ∧
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn p.val.2.val)).IsChain (· ≠ ·)}

/-- 概要：空語合成の非零候補の元の成功項は有限（BF §1.5.7–9）。
方針：有限な成功項の部分型の有限性を使う。
規約：係数環や非零性を仮定しない。
使われ方：nullary 部分合成の有限和の元添字。 -/
instance nullarySourceFintype {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k) := Fintype.ofFinite _

/-- 概要：同じ語を出力する同じ入力列の成功項は一致（BF §1.5.8–9）。
方針：基底語をリストの単射性、Schedule を既存の出力一意性で揃える。
規約：元の入力列の退化性には条件を課さない。
使われ方：成功項への選択写像の性質を語の等式で証明する。 -/
lemma successfulWord_eq_of_word_eq {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (p q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w)
    (he : List.ofFn p.val.2.val = List.ofFn q.val.2.val) : p = q := by
  have hv : p.val.2 = q.val.2 := Subtype.ext (List.ofFn_injective he)
  have hs : p.val.1 = q.val.1 := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_of_same_output w w p.val.1 q.val.1 p.val.2.val
    p.property (by rw [he]; exact q.property)
  exact Subtype.ext (Prod.ext hs hv)

/-- 概要：元の非零候補の成功項から実際の nullary 目標成功項へ写す（BF §1.5.7–9）。
方針：指定値削除による順方向成功から目標項を選ぶ。
規約：出力 arity は正で、選ぶ目標語は削除語と厳密に一致する。
使われ方：nullary 全単射の順方向写像。 -/
def nullaryForward {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ) :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_successfulWord_forward_exists hm w τ k p.val
    p.property.1 p.property.2)

/-- 概要：順方向成功項の語は元の指定値削除語（BF §1.5.7–9）。
方針：順方向の存在証明の選択条件を読む。
規約：成功 Schedule の選択に依存しない。
使われ方：目標項の等式と各項の値の保存を証明する。 -/
lemma nullaryForward_word {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k) :
    List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward hm w τ k p).val.2.val =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn p.val.val.2.val) :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_successfulWord_forward_exists hm w τ k p.val
    p.property.1 p.property.2)

/-- 概要：全ての実際の nullary 目標成功項は元の非零候補の成功項から来る（BF §1.5.7–9）。
方針：解放値探索による持ち上げを元の有限部分型へまとめ、語と Schedule の一意性で戻す。
規約：出力 arity は正。単射性はまだ主張しない。
使われ方：空語合成の全成功項の有限全単射の全射性。 -/
lemma nullaryForward_surjective {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward hm w τ k) := by
  intro q
  obtain ⟨p, hc, he⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullary_successfulWord_lift_exists w τ k q
  let p' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k := ⟨p, hc, by
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate q.val.2.val q.val.2.nondegenerate⟩
  refine ⟨p', ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.successfulWord_eq_of_word_eq _ _ _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_word]
  exact he

/-- 概要：有限な順方向写像は空語部分合成の各項の値を保つ（BF §1.2.4・§1.5.7–9）。
方針：一出現の空語合成の削除表示と目標成功語の式を連結する。
規約：任意の可換環と全次数、正の出力 arity。
使われ方：全単射を完成した後、有限和を実際の部分合成へ戻す。 -/
lemma nullaryForward_term (A : Type u) [CommRing A] {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 0) (d + 0) (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward hm w τ k p).val.2) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords_nullary_of_count_eq_one A _ _ _ p.property.1,
    ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullaryForward_word hm w τ k p, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
