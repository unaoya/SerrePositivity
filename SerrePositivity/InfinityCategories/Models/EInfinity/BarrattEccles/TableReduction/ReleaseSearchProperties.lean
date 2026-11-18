module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch

/-!
模型。文献の定義との比較は後で
# 解放値の探索の分割・先行抽出・一意性

概要：Berger–Fresse §1.4.4 の最初の変更行の探索を実際の逆抽出に使う。
方針：探索の各構成子から行分割と先行抽出を取り、異なる停止条件を排反にする。
規約：探索の最初の変更行と終端状態は一意。
使われ方：逆の行長移動の構成と、順方向から戻ることの検証に使う。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

namespace ReleaseSearch

variable {n : ℕ} {a : Fin n} {rs before after : List (List (Fin n) × ℕ)}
  {removed finish : List (Fin n)} {picked : List (List (Fin n))} {chosen : List (Fin n) × ℕ}

/-- 概要：探索の停止行とその前後は元の行リストを分割する（BF §1.4.4）。
方針：飛ばした各行を先行部分へ加える。
規約：停止行を一行だけ保つ。
使われ方：変更する後続行の実際の位置を指定する。 -/
lemma decomposition (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after) :
    rs = before ++ chosen :: after := by
  induction h with
  | hit => rfl
  | terminal => rfl
  | skip hr hb hx ht ih => simpa only [List.cons_append] using congrArg (List.cons _) ih

/-- 概要：探索で飛ばした先行行は解放状態で同じ選択語を持つ（BF §1.4.4）。
方針：未選択行の成功条件を先行抽出の構成子へ移す。
規約：元の reduceRows と同じ選択語と終端状態を保つ。
使われ方：逆の抽出の変更行までの実際の先行抽出を組み立てる。 -/
lemma toPrefix (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix before removed picked finish := by
  induction h with
  | hit => exact .nil _
  | terminal => exact .nil _
  | skip hr hb hx ht ih => exact .cons hr hb ih

/-- 概要：探索の先行出力には解放値が現れない（BF §1.4.4）。
方針：飛ばした各行の選択部分の不出現を連結する。
規約：停止行の選択値は含めない。
使われ方：順方向の早い除外と逆探索の出力を比較する。 -/
lemma not_mem_selected (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after) :
    a ∉ picked.flatten := by
  induction h with
  | hit => simp
  | terminal => simp
  | skip hr hb hx ht ih =>
    simp only [List.flatten_cons, List.mem_append, not_or]
    exact ⟨hx, ih⟩

/-- 概要：停止行では内部で出現するか、最後の延長で初めて出現する（BF §1.4.4）。
方針：探索の停止構成子の条件を読む。
規約：最後の延長の場合も元の選択部分には現れない。
使われ方：通常と最終末尾の二つの逆の局所挿入に分ける。 -/
lemma selection_cases (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after) :
    a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish chosen.1).take chosen.2 ∨
      (after = [] ∧ a ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish chosen.1).take chosen.2 ∧
        a ∈ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available finish chosen.1).take (chosen.2 + 1)) := by
  induction h with
  | hit ha => exact Or.inl ha
  | terminal hx ha => exact Or.inr ⟨rfl, hx, ha⟩
  | skip hr hb hx ht ih => exact ih

/-- 概要：最初の変更行の探索の分割・選択・終端状態は一意（BF §1.4.4）。
方針：停止と未選択の条件の矛盾を使い、通過する場合だけ後続を比較する。
規約：存在証明の選択に依存しない。
使われ方：逆対応の候補と順方向で得られる候補の一致を証明する。 -/
lemma unique (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before picked finish chosen after) :
    ∀ {before' picked' finish' chosen' after'},
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ReleaseSearch a rs removed before' picked' finish' chosen' after' →
        before = before' ∧ picked = picked' ∧ finish = finish' ∧
          chosen = chosen' ∧ after = after' := by
  induction h with
  | hit ha =>
    intro before' picked' finish' chosen' after' h'
    cases h' with
    | hit ha' => simp
    | terminal hx' ha' => exact False.elim (hx' ha)
    | skip hr' hb' hx' ht' => exact False.elim (hx' ha)
  | terminal hx ha =>
    intro before' picked' finish' chosen' after' h'
    cases h' with
    | hit ha' => exact False.elim (hx ha')
    | terminal hx' ha' => simp
    | skip hr' hb' hx' ht' => cases ht'
  | skip hr hb hx ht ih =>
    intro before' picked' finish' chosen' after' h'
    cases h' with
    | hit ha' => exact False.elim (hx ha')
    | terminal hx' ha' => cases ht
    | skip hr' hb' hx' ht' =>
      obtain ⟨he, hp, hf, hc, ha⟩ := ih ht'
      exact ⟨congrArg (List.cons _) he, congrArg (List.cons _) hp, hf, hc, ha⟩

end ReleaseSearch

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
