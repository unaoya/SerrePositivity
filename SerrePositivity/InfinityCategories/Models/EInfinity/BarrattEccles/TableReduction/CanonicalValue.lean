module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalUniqueness
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListDegeneracy

/-!
模型。文献の定義との比較は後で
# 標準置換列の table reduction の値

概要：Berger–Fresse §1.4.3 の標準頂点列の TR が元の全射語になることを証明する。
方針：標準 Schedule の抽出値を計算し、他の全ての項は退化または失敗で零とする。
規約：零 arity は空語の明示的な分岐で扱う。
使われ方：一般の TR の次数ごとの全射性と線形な切断を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

variable (A : Type u) [CommRing A]

/-- 概要：標準 Schedule の TR 項は元の語の生成元（BF §1.4.3）。
方針：全行の抽出の等式と語のリスト化の正規化を使う。
規約：正の arity で標準 Schedule を指定する。
使われ方：TR の有限和の唯一の非零項の値を計算する。 -/
lemma term_canonical {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule v hn) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_canonical v hn]
  simp only [Option.map_some, Option.getD_some, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn]

/-- 概要：標準以外の Schedule の TR 項は零（BF §1.4.3）。
方針：抽出に成功して非退化なら Schedule の一意性に反する。
規約：失敗する抽出も零を返す。
使われ方：有限和を標準項へ帰着する。 -/
lemma term_eq_zero_of_ne_canonical {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n)
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (hr : r ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule v hn) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) r = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term
  cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) r) [] with
  | none => rfl
  | some out =>
    simp only [Option.map_some, Option.getD_some]
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_eq_zero_of_not_isChain
    intro hc
    exact hr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_eq_canonical_of_isChain v hn r out h hc)

/-- 概要：正の arity で標準頂点列の TR は元の全射語（BF §1.4.3）。
方針：標準 Schedule の一項を取り出し、それ以外を零とする。
規約：係数環の標数や非零性の仮定を課さない。
使われ方：全射性の基底元の逆像を与える。 -/
lemma onSequence_canonical_of_pos {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (hn : 0 < n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v.val := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ite_eq_right (Nat.ne_of_gt hn)]
  rw [Finset.sum_eq_single (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSchedule v hn)]
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term_canonical A v hn
  · intro r _ hr
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term_eq_zero_of_ne_canonical A v hn r hr
  · simp

/-- 概要：全 arity で標準頂点列の TR は元の全射語（BF §1.4.3）。
方針：正の arity の式と空語の nullary 分岐を合わせる。
規約：arity 0 の正次数には基底語が存在しない。
使われ方：一般の TR の次数ごとの線形な全射性を得る。 -/
lemma onSequence_canonical {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A v.val := by
  cases n with
  | zero =>
    cases d with
    | zero =>
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ↓reduceIte]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn A v.val
    | succ d => exact isEmptyElim v
  | succ n => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_canonical_of_pos A v (Nat.zero_lt_succ n)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
