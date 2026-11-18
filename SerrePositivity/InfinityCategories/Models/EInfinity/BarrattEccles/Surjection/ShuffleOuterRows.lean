module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleTableRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.MonotoneCollapse

/-!
模型。文献の定義との比較は後で
# 実際の経路の圧縮外側行列と元の外側行数

概要：Berger–Fresse §1.5.8 の圧縮外側表の行列を元の置換列へ同定する。
方針：経路座標は単調で端点を保つ単位歩幅写像なので、繰り返しを縮めて元の列に戻る。
規約：元の外側列が隣接非一致なら元の行列そのものと一致する。
使われ方：復元外側表に元の次数の Schedule を構成するための行数を供給する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：経路の水平座標で繰り返した列の縮約は元の列の縮約（BF §1.5.8）。
方針：水平座標の端点・単調性・単位歩幅を一般の有限順序縮約へ渡す。
規約：値列に非退化性はまだ課さない。
使われ方：経路上の外側逆置換行の繰り返しを除く。 -/
lemma collapse_horizontal_ofFn {α : Type*} [DecidableEq α] {d e : ℕ}
    (s : ShufflePath d e) (g : Fin (d + 1) → α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun i => g (s.horizontal i))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn g) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_ofFn_orderHom (d + e) d s.horizontal
    s.horizontal_endpoints.1 s.horizontal_endpoints.2
  intro i
  rcases s.unit_step i with h | h
  · omega
  · have hv := congrArg Fin.val h.1; omega

/-- 概要：経路の垂直座標で繰り返した列の縮約は元の列の縮約（BF §1.5.8）。
方針：垂直座標の端点・単調性・単位歩幅を一般の有限順序縮約へ渡す。
規約：値列の空間は任意の決定可能な等号を持つ型。
使われ方：逆構成で元の内側行列の繰り返しを照合する。 -/
lemma collapse_vertical_ofFn {α : Type*} [DecidableEq α] {d e : ℕ}
    (s : ShufflePath d e) (g : Fin (e + 1) → α) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun i => g (s.vertical i))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn g) := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_ofFn_orderHom (d + e) e s.vertical
    s.vertical_endpoints.1 s.vertical_endpoints.2
  intro i
  rcases s.unit_step i with h | h
  · have hv := congrArg Fin.val h.2; omega
  · omega

/-- 概要：行数が合う外側復元表は元の全外側逆置換行を持つ（BF §1.5.8）。
方針：同時帰納法で zipWith の全行対応を計算する。
規約：この行列の等式は行長の選択に依存しない。
使われ方：圧縮前の復元外側行列を元の経路の外側列へ戻す。 -/
lemma recoveredOuterTable_fst {m n : ℕ} (k : Fin (m + 1))
    (entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (picked : List (List (Fin (m + n)))) (hl : entries.length = picked.length) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k entries picked).map Prod.fst =
      entries.map (fun p => List.ofFn p.1.symm) := by
  induction entries generalizing picked with
  | nil => cases picked <;> simp_all [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable]
  | cons entry entries ih =>
    cases picked with
    | nil => simp only [List.length_cons, List.length_nil] at hl; omega
    | cons word picked =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable, List.zipWith_cons_cons, List.map_cons]
      exact congrArg (List.ofFn entry.1.symm :: ·) (ih picked hl)

/-- 概要：実際の経路から復元した圧縮外側行列は元の行列の縮約（BF §1.5.8）。
方針：圧縮行列の表示と水平座標の繰り返し縮約を合わせる。
規約：元の外側置換列に隣接重複を許す。
使われ方：元の非退化な置換列に特殊化して外側の行列と次数を同定する。 -/
lemma shuffle_compressed_outer_rows {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r))
      removed picked finish) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).map
      Prod.fst = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (List.ofFn (fun j => List.ofFn (outer j).symm)) := by
  have hl : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r).length = picked.length := by
    simpa only [List.length_map, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable] using (congrArg List.length hp.lengths).symm
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows_fst, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable_fst _ _ _ hl]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries, List.map_ofFn, Function.comp_def]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_horizontal_ofFn s (fun j => List.ofFn (outer j).symm)

/-- 概要：逆置換の全行は元の置換を一意に決める（BF §1.5.8）。
方針：ofFn の単射性から逆置換を一致させ、再び逆置換を取る。
規約：零 arity も含む。
使われ方：元の置換列の隣接非一致を逆置換行列へ渡す。 -/
lemma permutation_inverse_row_injective (n : ℕ) :
    Function.Injective (fun σ : Equiv.Perm (Fin n) => List.ofFn σ.symm) := by
  intro σ τ h
  have hf := List.ofFn_injective h
  have hs : σ.symm = τ.symm := Equiv.ext (fun j => congrFun hf j)
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs

/-- 概要：隣接非一致の元の置換列から復元した圧縮外側行列は元の行列（BF §1.5.8）。
方針：元の置換列の非退化性を逆置換行へ渡し、行列の縮約を除く。
規約：出力語の非退化性はこの行列の照合に不要。
使われ方：元の外側表と同じ行数・次数で Schedule を復元する。 -/
lemma shuffle_compressed_outer_rows_of_isChain {m n d e : ℕ}
    (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r))
      removed picked finish) (hne : (List.ofFn outer).IsChain (· ≠ ·)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).map
      Prod.fst = List.ofFn (fun j => List.ofFn (outer j).symm) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_compressed_outer_rows k s outer inner r removed finish picked hp]
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse_eq_self
  apply List.isChain_ofFn.mpr
  intro i hi he
  exact (List.isChain_ofFn.mp hne i hi) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.permutation_inverse_row_injective _ he)

/-- 概要：非退化な元の外側列の圧縮復元表は元の次数＋1 行（BF §1.5.8）。
方針：元の外側行列との一致の長さを取る。
規約：内側次数に由来する繰り返しは圧縮で全て除かれる。
使われ方：元の外側次数の実際の Schedule の有限添字型を決める。 -/
lemma shuffle_compressed_outer_length {m n d e : ℕ} (k : Fin (m + 1)) (s : ShufflePath d e)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e))
    (removed finish : List (Fin (m + n))) (picked : List (List (Fin (m + n))))
    (hp : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r))
      removed picked finish) (hne : (List.ofFn outer).IsChain (· ≠ ·)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compressRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.recoveredOuterTable k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffleTableEntries s outer inner r) picked)).length =
      d + 1 := by
  have h := congrArg List.length
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_compressed_outer_rows_of_isChain k s outer inner r removed finish picked hp hne)
  simpa only [List.length_map, List.length_ofFn] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
