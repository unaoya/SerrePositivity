module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DegreeZero

/-!
模型。文献の定義との比較は後で
# Table reduction の次数零と零入力成分

概要：Berger–Fresse §1.3.1 の有限和を次数零で逆置換の一行表示と同定する。
方針：一行の行長の選択が一意であることから和を一項へ簡約する。
規約：arity 0 では空語を返す明示的な分岐を使う。
使われ方：一般の TR の単位と nullary 演算の比較の基礎となる。
-/

@[expose] public section

noncomputable section


universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：次数零で行長の選択は高々一つ（BF §1.3.1）。
方針：一行の長さは総和から n と定まる。
規約：arity 0 では選択が存在しなくても成立する。
使われ方：TR の次数零の和を単一の行へ帰着する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.instSubsingletonScheduleOfNatNat (n : ℕ) : Subsingleton (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n 0) where
  allEq r s := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    have hsum (t : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n 0) :
        (∑ j, (t.val j).val) = (t.val 0).val := by
      apply Finset.sum_eq_single 0
      · intro j _ hj
        exact False.elim (hj (Fin.ext (by omega)))
      · simp
    have hr := r.property.2
    have hs := s.property.2
    rw [hsum r] at hr
    rw [hsum s] at hs
    have hi : i = 0 := Fin.ext (by omega)
    simpa only [hi] using hr.trans hs.symm


/-- 概要：正の arity の次数零で唯一の行長の選択（BF §1.3.1）。
方針：唯一の行に n 個の文字を指定する。
規約：n が正であるときだけ構成する。
使われ方：次数零の和の既定元を与える。 -/
def degreeZeroSchedule {n : ℕ} (hn : 0 < n) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n 0 :=
  ⟨fun _ => ⟨n, Nat.lt_succ_self n⟩, (fun _ => hn), by simp⟩

variable (A : Type u) [CommRing A]

/-- 概要：正の arity の次数零の TR は逆置換の語（BF §1.3.1）。
方針：行長の選択を一意な一項へ簡約し、一行の抽出を計算する。
規約：BE の置換は位置の作用として与えられる。
使われ方：TR の単位保存と次数零の比較に用いる。 -/
lemma onSequence_degree_zero {n : ℕ} (hn : 0 < n)
    (w : Fin 1 → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (d := 0) (fun i => (w 0)⁻¹ i) := by
  let : Unique (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n 0) :=
    { default := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.degreeZeroSchedule hn, uniq := fun _ => Subsingleton.elim _ _ }
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ite_eq_right (by omega), Fintype.sum_unique]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.degreeZeroSchedule hn) = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.degreeZeroSchedule, List.ofFn_succ, List.ofFn_zero,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available, List.not_mem_nil, not_false_eq_true, decide_true,
    List.filter_true, List.length_ofFn, Nat.le_refl, and_true, ite_eq_left hn,
    Option.map_some, List.append_nil, Option.getD_some]
  rw [List.take_of_length_le (by simp)]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn A _


/-- 概要：nullary 次数零の TR は空語（BF §0・§1.3.1）。
方針：明示した arity 0 の分岐を評価する。
規約：正の行長を持つ table の公式はここでは使わない。
使われ方：零入力演算の比較を供給する。 -/
@[simp] lemma onSequence_nullary_zero (w : Fin 1 → Equiv.Perm (Fin 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (n := 0) (d := 0) [] := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ↓reduceIte]

/-- 概要：nullary 正次数の TR は零（BF §0・§1.2.1）。
方針：arity 0 の正次数の分岐を評価する。
規約：値域には基底語が存在しない。
使われ方：TR の全 arity での定義の境界を検証する。 -/
@[simp] lemma onSequence_nullary_succ (d : ℕ)
    (w : Fin (d + 1 + 1) → Equiv.Perm (Fin 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = (0 : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A 0 (d + 1)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ↓reduceIte, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
