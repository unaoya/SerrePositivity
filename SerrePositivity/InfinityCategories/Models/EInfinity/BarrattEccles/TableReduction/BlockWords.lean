module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.BlockCoordinates
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReceiverStep

/-!
模型。文献の定義との比較は後で
# Schedule の二行の語と利用可能長の余裕

概要：Berger–Fresse §1.4.4 の実際の抽出から行長移動の語の分割を導く。
方針：置換行の重複のなさ、出力座標の照合、後続の二つの異なる値を使う。
規約：全ての条件を元の成功 Schedule から得る。
使われ方：受け取り行と削除行の局所抽出へ入力を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：置換の行は全ての値を含み重複しない（BF §1.3.1）。
方針：逆置換の全射性と単射性を ofFn に移す。
規約：arity 零も含む。
使われ方：後続に現れる別の値が受け取り行でも利用可能であることを示す。 -/
lemma vertexRow_nodup {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n)) (i : Fin m) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i).Nodup := List.nodup_ofFn_ofInjective (w i).symm.injective

/-- 概要：全ての値は任意の置換行に現れる（BF §1.3.1）。
方針：逆置換の逆像を所属の証人とする。
規約：値がある全 arity で成立する。
使われ方：後続の選択値を現在行の長さの余裕へ移す。 -/
lemma mem_vertexRow {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n)) (i : Fin m) (a : Fin n) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i := by
  apply List.mem_ofFn.mpr
  exact ⟨w i a, (w i).symm_apply_apply a⟩

/-- 概要：重複のない語を指定要素の位置で前後に分ける（BF §1.4.4）。
方針：take・指定要素・drop の分割に重複のなさを適用する。
規約：指定要素は前後の部分に現れない。
使われ方：削除行の利用可能語を削除値で分割する。 -/
lemma nodup_split_at {α : Type*} (xs : List α) (hn : xs.Nodup) (j : Fin xs.length) :
    ∃ pre post, xs = pre ++ xs[j.val] :: post ∧ pre.length = j.val ∧
      xs[j.val] ∉ pre ∧ xs[j.val] ∉ post := by
  let pre := xs.take j.val
  let post := xs.drop (j.val + 1)
  have he : xs = pre ++ xs[j.val] :: post := by
    calc
      _ = xs.take j.val ++ xs.drop j.val := (List.take_append_drop j.val xs).symm
      _ = _ := by rw [List.drop_eq_getElem_cons j.isLt]
  have hp := List.nodup_append.mp ((congrArg List.Nodup he).mp hn)
  refine ⟨pre, post, he, ?_, ?_, (List.nodup_cons.mp hp.2.1).1⟩
  · simp only [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt j.isLt)]
  · intro hm
    exact hp.2.2 _ hm _ (List.mem_cons_self ..) rfl

namespace ScheduleBlock

variable {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
  {receiver donor : Fin (d + 1)} {out : List (Fin n)}

/-- 概要：直前出現の値は受け取り行で早く除外する実際の末尾値（BF §1.4.4）。
方針：出力座標の値を take の末尾公式へ代入する。
規約：元の末尾位置と削除位置の値の一致を指定する。
使われ方：受け取り行延長の入力を元の成功抽出から得る。 -/
lemma receiver_selected_end (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (p k : Fin out.length)
    (hp : p.val + 1 = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver + (r.val receiver).val)
    (hv : out[p.val] = out[k.val]) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take ((r.val receiver).val - 1) ++
        [out[k.val]] := by
  have hr := r.property.1 receiver
  have hb := b.receiver_bound
  have hi : (r.val receiver).val - 1 < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).length := by
    omega
  have he := List.take_succ_eq_append_getElem hi
  have heq : (r.val receiver).val - 1 + 1 = (r.val receiver).val := by omega
  have hvalue := (b.receiver_end_value p hp).symm.trans hv
  simpa only [heq, hvalue] using he

/-- 概要：削除行の利用可能語を実際の削除値の前後へ分ける（BF §1.4.4）。
方針：行内座標の値と置換行の重複のなさを適用する。
規約：前後の語には削除値がないことも保持する。
使われ方：通常・最終末尾の donor step に全ての語の条件を渡す。 -/
lemma donor_split (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (k : Fin out.length)
    (hl : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ≤ k.val)
    (hh : k.val < _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor + (r.val donor).val) :
    ∃ pre post, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor) = pre ++ out[k.val] :: post ∧
      pre.length = k.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor ∧ out[k.val] ∉ pre ∧ out[k.val] ∉ post := by
  let j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).length :=
    ⟨k.val - _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor, by have := b.donor_bound; omega⟩
  have hn : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).Nodup :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow_nodup w donor).filter (fun a => a ∉ b.finish)
  obtain ⟨pre, post, he, hp, hpre, hpost⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nodup_split_at (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)) hn j
  have hv : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor))[j.val] = out[k.val] :=
    b.donor_value k hl hh
  rw [hv] at he hpre hpost
  exact ⟨pre, post, he, hp, hpre, hpost⟩

/-- 概要：元の中間行と削除行以降の全抽出は証明書の後続語を返す（BF §1.4.4）。
方針：削除行の成功を再構成し、中間行の証跡を連結する。
規約：変更前の元の抽出を使う。
使われ方：後続の別の値から受け取り行の利用可能長を評価する。 -/
lemma after_receiver_success (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (b.middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: b.after)
      (b.removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take ((r.val receiver).val - 1)) =
        some (b.picked.flatten ++
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++ b.tail)) := by
  have hd := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success _ _ _ _ _ (r.property.1 donor) b.donor_bound b.tail_success
  exact b.middle_trace.append _ _ hd

/-- 概要：削除行の長さ 2 以上から受け取り行の実際の延長余裕を導く（BF §1.4.4）。
方針：後続の重複のない二文字以上の選択語から末尾値と違う値を取る。
規約：arity の余裕を入力せず実際の利用可能長を評価する。
使われ方：全ての成功した最終出現削除の受け取り行を一文字延長する。 -/
lemma receiver_capacity (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) (a : Fin n)
    (hd : 1 < (r.val donor).val)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take ((r.val receiver).val - 1) ++ [a]) :
    (r.val receiver).val < (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).length := by
  let selected := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val
  have hn : selected.Nodup := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow_nodup w donor).filter _).take
  have hlen : selected.length = (r.val donor).val := b.donor_take_length
  have hother : ∃ c ∈ selected, c ≠ a := by
    by_contra hx
    have hs : selected ⊆ [a] := by
      intro c hc
      simp only [List.mem_singleton]
      by_contra hne
      exact hx ⟨c, hc, hne⟩
    have hb := hn.length_le_of_subset hs
    simp only [List.length_singleton] at hb
    omega
  obtain ⟨c, hc, hne⟩ := hother
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.receiver_capacity_of_tail b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver) (r.val receiver).val a c
    he _ _ b.after_receiver_success _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_vertexRow w receiver c) hne
  exact List.mem_append_right _ (List.mem_append_left _ hc)

end ScheduleBlock

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
