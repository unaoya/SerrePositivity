module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CompositionPositive
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegreeZero
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEdges

/-!
模型。文献の定義との比較は後で
# 内側 arity 零・正次数の TR 合成保存

概要：Berger–Fresse §1.5 の nullary 境界で、内側の正次数は退化項だけとなることを証明する。
方針：各 shuffle の垂直辺で内側置換の一意性により合成頂点が重なり、TR 全体を零にする。
規約：外側 arity・次数は任意で、外側出力 arity 零も含む。
使われ方：全 arity の合成保存を、内側次数零の空語挿入だけへ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：内側 arity 零・正次数の各実際の shuffle 列の TR は零（BF §1.5 の nullary 境界）。
方針：実際の垂直辺を一つ取り、空集合の置換の一意性で隣接合成頂点を一致させる。
規約：外側列は任意。内側の退化性を入力に要求しない。
使われ方：nullary 正次数の全 shuffle 符号付き和の零性。 -/
lemma onSequence_shuffle_nullary_succ (m d e : ℕ) (k : Fin (m + 1))
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1 + 1) → Equiv.Perm (Fin 0)) (s : ShufflePath d (e + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j => permutationComposition m 0 k (outer (s.horizontal j))
      (inner (s.vertical j))) = 0 := by
  obtain ⟨a, _, _, hfixed⟩ := s.vertical_edge (⟨0, by omega⟩ : Fin (e + 1))
  let w := fun j => permutationComposition m 0 k (outer (s.horizontal j)) (inner (s.vertical j))
  have hw : w a.castSucc = w a.succ := by
    change permutationComposition m 0 k (outer (s.horizontal a.castSucc))
      (inner (s.vertical a.castSucc)) = _
    rw [hfixed, Subsingleton.elim (inner (s.vertical a.castSucc)) (inner (s.vertical a.succ))]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_zero_of_adjacent_eq A w a.castSucc a.succ rfl hw

/-- 概要：内側 arity 零・正次数の全 onSequence shuffle 和も部分合成を保つ（BF §1.5 の nullary 境界）。
方針：全実際の経路項と内側 TR がともに零となることを使う。
規約：任意の可換環と全外側次数。
使われ方：nullary 合成保存の正の内側次数の場合。 -/
lemma onSequence_partialComposition_nullary_succ {m d e : ℕ} (k : Fin (m + 1))
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1 + 1) → Equiv.Perm (Fin 0)) :
    (∑ s : ShufflePath d (e + 1), (s.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j =>
      permutationComposition m 0 k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d (e + 1) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A outer) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_shuffle_nullary_succ, smul_zero, Finset.sum_const_zero,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_succ, map_zero]

/-- 概要：nullary 正次数の正規化生成元の shuffle 合成で TR は部分合成を保つ（BF §1.5）。
方針：正規化生成元の全 shuffle 公式に実際の退化列の零性を適用する。
規約：元の単体の非退化性は要求しない。
使われ方：任意の正規化鎖の合成保存を双線形外延性で証明する。 -/
lemma normalizedMap_shuffle_generators_nullary_succ {m d e : ℕ} (k : Fin (m + 1))
    (x : (simplicial (m + 1)) _⦋d⦌) (y : (simplicial 0) _⦋e + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 0) (d + (e + 1))
      (shuffleBilinear A m 0 k d (e + 1) (normalizedGenerator A (m + 1) d x)
        (normalizedGenerator A 0 (e + 1) y)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d (e + 1) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d (normalizedGenerator A (m + 1) d x))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A 0 (e + 1) (normalizedGenerator A 0 (e + 1) y)) := by
  simp only [shuffleBilinear_generators, shuffleValue, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_generator]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_partialComposition_nullary_succ A k (simplexEquiv (m + 1) d x)
    (simplexEquiv 0 (e + 1) y)]
  apply Finset.sum_congr rfl
  intro s _
  congr 1

/-- 概要：内側 arity 零・正次数で実際の正規化 TR は全双線形 shuffle 合成を保つ（BF §1.5）。
方針：両辺を双線形写像として正規化生成元の零項公式で一致させる。
規約：全外側 arity・次数と任意の可換環。
使われ方：全 arity の TR 合成保存で残りを内側次数零の空語だけに限定する。 -/
lemma normalizedMap_shuffleBilinear_nullary_succ {m d e : ℕ} (k : Fin (m + 1))
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A (m + 1)).X d)
    (y : (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedChains A 0).X (e + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 0) (d + (e + 1)) (shuffleBilinear A m 0 k d (e + 1) x y) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d (e + 1) k
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d x) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A 0 (e + 1) y) := by
  let L := (shuffleBilinear A m 0 k d (e + 1)).compr₂
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 0) (d + (e + 1)))
  let R := ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d (e + 1) k).compl₂
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A 0 (e + 1))).comp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 1) d)
  have he : L = R := by
    apply normalizedGenerator_bilinear_ext A (m + 1) 0 d (e + 1)
    intro sx sy
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap A (m + 0) (d + (e + 1))
      (shuffleBilinear A m 0 k d (e + 1) (normalizedGenerator A (m + 1) d sx)
        (normalizedGenerator A 0 (e + 1) sy)) = _
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.normalizedMap_shuffle_generators_nullary_succ A k sx sy
  exact congrArg (fun f => f x y) he

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
