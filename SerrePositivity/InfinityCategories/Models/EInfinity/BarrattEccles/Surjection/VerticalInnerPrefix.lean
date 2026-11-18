module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalInnerStep

/-!
模型。文献の定義との比較は後で
# 垂直成分の有限先行部分の内側抽出

概要：Berger–Fresse §1.5.8 の固定外側頂点の連続行を内側表へ射影する。
方針：実際の後続成功と全出力の非退化性から各選択末尾の保持を導く。
規約：垂直成分の最終行の直前までを先行部分とし、最終行以降も成功を要求する。
使われ方：逆構成で元の内側 table の連続する行長・選択語・除外状態を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：固定外側頂点の内側置換と行長から実際の合成表を作る（BF §1.5.8）。
方針：各内側置換を外側置換へ合成し、その逆置換行と行長を組にする。
規約：元の行長をそのまま保持する。
使われ方：垂直成分の任意の有限先行部分を記述する。 -/
def verticalTable {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) : List (List (Fin (m + n)) × ℕ) :=
  entries.map (fun p => (List.ofFn (permutationComposition m n k σ p.1).symm, p.2))

/-- 概要：垂直成分の非最終選択行の末尾は全て内側射影で残る（BF §1.5.8）。
方針：先行行で帰納し、各段階の実際の後続成功と非退化性へ行末制約を適用する。
規約：選択語だけからの仮定を追加せず、元の抽出証跡と後続成功から結論する。
使われ方：先行抽出全体を内側に射影するための末尾条件を供給する。 -/
lemma vertical_prefix_last_retained {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) removed picked finish)
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·)) :
    ∀ word ∈ picked, ∃ a b, word.getLast? = some a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some b := by
  induction entries generalizing removed picked with
  | nil => cases hpre; simp
  | cons entry entries ih =>
    obtain ⟨τ, r⟩ := entry
    have hfull := hpre.append
      ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest) tail hrest
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries)
      removed picked finish at hpre
    cases hpre with
    | @cons _ _ _ _ picked _ hr hb ht =>
      have hfirst : ∃ a b, ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
          (List.ofFn (permutationComposition m n k σ τ).symm)).take r).getLast? = some a ∧
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some b := by
        cases entries with
        | nil =>
          exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_last_retained σ τ τlast k removed _
            r s rest (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable, List.map_cons, List.map_nil,
              List.cons_append, List.nil_append] using hfull) hc
        | cons entry entries =>
          exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_last_retained σ τ entry.1 k removed _
            r entry.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries ++
              (List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
            (by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable, List.map_cons, List.cons_append] using hfull) hc
      have hc' : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
          (List.ofFn (permutationComposition m n k σ τ).symm)).take r ++
          (picked.flatten ++ tail)).IsChain (· ≠ ·) := by
        simpa only [List.flatten_cons, List.append_assoc] using hc
      have htail := ih _ _ ht hc'.right_of_append
      intro word hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hfirst
      · exact htail word hw

/-- 概要：垂直成分の非最終先行部分は実際の内側抽出へ射影できる（BF §1.5.8）。
方針：全選択末尾の内側性を元の成功から導き、部分射影の証跡定理へ渡す。
規約：選択語と終端除外状態は元のものの内側射影を保つ。
使われ方：任意の成功合成表から元の内側 table を構成する連続部分。 -/
lemma vertical_prefix_inner_projection {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ)) (τlast : Equiv.Perm (Fin n))
    (s : ℕ) (rest : List (List (Fin (m + n)) × ℕ))
    (removed finish tail : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) removed picked finish)
    (hrest : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τlast).symm, s) :: rest)
      finish = some tail) (hc : (picked.flatten ++ tail).IsChain (· ≠ ·)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) picked)
      (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (picked.map (List.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)))
      (finish.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) :=
  hpre.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.vertical_prefix_last_retained σ k entries τlast s rest removed finish tail picked
      hpre hrest hc)

/-- 概要：射影した垂直先行部分の全行は元の内側逆置換列（BF §1.5.8）。
方針：証跡の行数一致から全行の射影を計算し、逆合成置換行の射影式を使う。
規約：この行列の一致自体には非退化性や後続成功を要求しない。
使われ方：射影成功を元の内側 table の成功として使う。 -/
lemma vertical_prefix_inner_rows {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin n) × ℕ))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hpre : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) removed picked finish) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries) picked).map Prod.fst =
      entries.map (fun p => List.ofFn p.1.symm) := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable σ k entries).length = picked.length := by
    simpa only [List.length_map] using (congrArg List.length hpre.lengths).symm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMapRows_fst _ _ _ hl]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.verticalTable, List.map_map, Function.comp_def,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_permutationComposition_row]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
