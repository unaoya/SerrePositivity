module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.TwoRowExtraction

/-!
模型。文献の定義との比較は後で
# 実際の Schedule の二行の抽出データ

概要：Berger–Fresse §1.4.4 の行長移動の全境界状態と出力位置を同じ証明書へまとめる。
方針：二行の分割・先行抽出・行長の和の公式を組み合わせる。
規約：抽出データは元の reduceRows で検証され、別の抽出模型を仮定しない。
使われ方：直前出現・削除値の位置から局所ブロック比較の入力を導く。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：BE の頂点を逆置換の一行表示で読む（BF §1.3.1）。
方針：既存 rows と同じ ofFn で並べる。
規約：右作用の規約に合わせて逆元を使う。
使われ方：二行の抽出証明書の各行を短く指定する。 -/
def vertexRow {n m : ℕ} (w : Fin m → Equiv.Perm (Fin n)) (i : Fin m) : List (Fin n) :=
  List.ofFn (fun k => (w i)⁻¹ k)

/-- 概要：実際の Schedule の二つの行の間の抽出状態と位置の証明書（BF §1.4.4）。
方針：元の行の分割と抽出証跡、全出力と開始位置を保持する。
規約：受け取り行と削除行の順序は構成時に使う。
使われ方：最終出現の行長移動に必要な語の位置・不出現を導く。 -/
structure ScheduleBlock {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (receiver donor : Fin (d + 1)) (out : List (Fin n)) where
  before : List (List (Fin n) × ℕ)
  middle : List (List (Fin n) × ℕ)
  after : List (List (Fin n) × ℕ)
  selectedBefore : List (List (Fin n))
  removed : List (Fin n)
  picked : List (List (Fin n))
  finish : List (Fin n)
  tail : List (Fin n)
  split : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) ::
    (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: after)
  before_length : before.length = receiver.val
  middle_length : before.length + 1 + middle.length = donor.val
  before_trace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before [] selectedBefore removed
  receiver_bound : (r.val receiver).val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).length
  middle_trace : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix middle
    (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take ((r.val receiver).val - 1))
      picked finish
  donor_bound : (r.val donor).val ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).length
  tail_success : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows after
    (finish ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take ((r.val donor).val - 1)) = some tail
  output_eq : out = selectedBefore.flatten ++
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val ++
      (picked.flatten ++ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val ++ tail)))
  prefix_length : selectedBefore.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver
  donor_start : selectedBefore.flatten.length + (r.val receiver).val + picked.flatten.length =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r donor

/-- 概要：成功した table の順序付き二行から実際の抽出データを構成（BF §1.4.4）。
方針：有限列の分割と先行抽出を取り出し、開始位置を行長の和で照合する。
規約：任意の成功出力を扱い、非退化性を要求しない。
使われ方：最終出現削除の二行を入力に局所比較のための状態を確保する。 -/
lemma scheduleBlock_nonempty {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (receiver donor : Fin (d + 1)) (ho : receiver < donor)
    (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) := by
  obtain ⟨before, middle, after, he, hb, hm⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ofFn_split_two
    (fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w i, (r.val i).val)) receiver donor ho
  have hsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) ::
      (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: after) := he
  have hsuccess : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) ::
      (middle ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: after)) [] = some out := by
    rw [← hsplit]; exact h
  obtain ⟨selectedBefore, removed, picked, finish, tail, hp, _, hr, hmid, _, hd, ht, hout⟩ :=
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.two_row_extraction before middle after _ _ _ _ [] out hsuccess
  have hprefix := hp.output_length
  have hmiddle := hmid.output_length
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r before _ hsplit receiver hb
  have hstart : selectedBefore.flatten.length = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleOffset r receiver := hprefix.trans hs
  have hdonorsplit : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r =
      (before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) :: middle) ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor, (r.val donor).val) :: after := by
    simpa only [List.append_assoc, List.cons_append] using hsplit
  have hdonorlen : (before ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver, (r.val receiver).val) :: middle).length =
      donor.val := by
    simp only [List.length_append, List.length_cons]
    omega
  have hsum := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_prefix_sum w r _ _ hdonorsplit donor hdonorlen
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at hsum
  refine ⟨⟨before, middle, after, selectedBefore, removed, picked, finish, tail,
    hsplit, hb, hm, hp, hr, hmid, hd, ht, hout, hstart, ?_⟩⟩
  omega

/-- 概要：受け取り行の選択語の長さは指定された行長（BF §1.4.4）。
方針：成功条件の上界で take の長さを評価する。
規約：語の値や後続状態には依存しない。
使われ方：出力の区間の境界を行長で計算する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.receiver_take_length {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.removed (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w receiver)).take (r.val receiver).val).length =
      (r.val receiver).val := by
  rw [List.length_take, Nat.min_eq_left b.receiver_bound]

/-- 概要：削除行の選択語の長さは指定された行長（BF §1.4.4）。
方針：成功条件の上界で take の長さを評価する。
規約：語の値や後続状態には依存しない。
使われ方：削除位置の行内添字を作る。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock.donor_take_length {n d : ℕ}
    {w : Fin (d + 1) → Equiv.Perm (Fin n)} {r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d}
    {receiver donor : Fin (d + 1)} {out : List (Fin n)}
    (b : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleBlock w r receiver donor out) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available b.finish (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.vertexRow w donor)).take (r.val donor).val).length =
      (r.val donor).val := by
  rw [List.length_take, Nat.min_eq_left b.donor_bound]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
