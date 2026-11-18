module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.OutputCoverage
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListDegeneracy
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OccurrenceSuffixes
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
模型。文献の定義との比較は後で
# 各入力列の成功 Schedule と基底語による有限和

概要：Berger–Fresse §1.3.1・§1.5.6 の元の TR 和を、成功する非退化基底語の有限型へ移す。
方針：成功出力の長さ・全射性・非退化性で基底語を構成し、零項を有限和の外へ出す。
規約：語を元の Schedule と組にして成功等式を保持する。正の arity の onSequence を展開する。
使われ方：元の成功二表と分割の和を二つの onSequence の部分合成へ戻す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：非退化な成功出力は本来の次数の非退化全射基底語である（BF §1.3.1）。
方針：実際の成功長で有限語を作り、出力の全射性と非退化性を移す。
規約：元の基底語を仮定せず、実際の出力から構成する。
使われ方：成功した各 Schedule の項を実際の基底ベクトルとして記述する。 -/
lemma word_exists_of_success {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (out : List (Fin n)) (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some out)
    (hc : out.IsChain (· ≠ ·)) : ∃ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d, List.ofFn v.val = out := by
  have hlen : out.length = n + d := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_length w r out h
  let f : Fin (n + d) → Fin n := fun i => out[i.val]'(by rw [hlen]; exact i.isLt)
  have hf : List.ofFn f = out := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  have hs : Function.Surjective f := by
    intro a
    have ha : a ∈ List.ofFn f := by rw [hf]; exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.output_covers w r out h a
    exact List.mem_ofFn.mp ha
  have hn : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate f := by
    have hc' : (List.ofFn f).IsChain (· ≠ ·) := by rw [hf]; exact hc
    intro i j hij
    have hb : i.val + 1 < n + d := by omega
    have he := List.isChain_ofFn.mp hc' i.val hb
    change f i ≠ f ⟨i.val + 1, hb⟩ at he
    have hi : (⟨i.val + 1, hb⟩ : Fin (n + d)) = j := Fin.ext hij
    simpa only [hi] using he
  exact ⟨⟨f, hs, hn⟩, hf⟩

/-- 概要：指定した置換列の実際の成功 Schedule と基底語（BF §1.3.1・§1.5.6）。
方針：Schedule と本来の次数の BasisWord の有限な直積を成功等式で制限する。
規約：退化出力・失敗は含めない。
使われ方：元の各 TR を基底語の成功項の和に展開する添字。 -/
abbrev SuccessfulWord {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) :=
  {p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w p.1) [] = some (List.ofFn p.2.val)}

/-- 概要：各列の全成功 Schedule と基底語の添字は有限（BF §1.5.6）。
方針：二つの有限型の直積の部分型の有限性を使う。
規約：実際の成功を仮定した有限性は追加しない。
使われ方：各 onSequence の成功基底語の有限和。 -/
noncomputable instance successfulWordFintype {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) : Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w) := Fintype.ofFinite _

variable (A : Type u) [CommRing A]

/-- 概要：各 table 項はその Schedule で成功する全基底語への指示関数和（BF §1.3.1）。
方針：失敗・退化なら零、非退化成功なら唯一の実際の基底語の一点和へ戻す。
規約：係数環の非零性を仮定しない。
使われ方：元の Schedule 和を成功 Schedule と基底語の有限型へ移す。 -/
lemma term_eq_sum_words {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A w r = ∑ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d,
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] = some (List.ofFn v.val)
        then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up v) else 0 := by
  classical
  cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r) [] with
  | none => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, h, Option.map_none, Option.getD_none, reduceCtorEq, ite_false,
      Finset.sum_const_zero]
  | some out =>
    by_cases hc : out.IsChain (· ≠ ·)
    · obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.word_exists_of_success w r out h hc
      have hp (v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : out = List.ofFn v'.val ↔ v = v' := by
        rw [← hv]
        constructor
        · intro he
          exact Subtype.ext (List.ofFn_injective he)
        · intro he
          rw [he]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, h, Option.map_some, Option.getD_some, ← hv, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word]
      have hi (v' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : List.ofFn v.val = List.ofFn v'.val ↔ v = v' := by
        rw [hv]
        exact hp v'
      simp only [Option.some.injEq, hi]
      symm
      exact Finset.sum_ite_eq_of_mem _ v _ (Finset.mem_univ v)
    · have hbad (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) : out ≠ List.ofFn v.val := by
        intro he
        apply hc
        rw [he]
        exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.isChain_ofFn_of_nondegenerate v.val v.nondegenerate
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, h, Option.map_some, Option.getD_some,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_eq_zero_of_not_isChain A out hc, Option.some.injEq, hbad, ite_false,
        Finset.sum_const_zero]

/-- 概要：正の arity の onSequence は全成功 Schedule と基底語の基底和（BF §1.3.1・§1.5.6）。
方針：各項の指示関数和を直積和へまとめ、成功部分型の有限和へ移す。
規約：元の退化・失敗 Schedule は零として全て含める。
使われ方：部分合成の両線形性で元の成功二表と分割の和を展開する。 -/
lemma onSequence_eq_sum_successfulWords {n d : ℕ} (hn : 0 < n)
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w = ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up p.val.2) := by
  classical
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ite_eq_right (show n ≠ 0 by omega)]
  simp_rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term_eq_sum_words]
  change (∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d, ∑ v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d,
    (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d =>
      if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w p.1) [] = some (List.ofFn p.2.val)
        then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up p.2) else 0) (r, v)) = _
  rw [← Fintype.sum_prod_type (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d =>
    if _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w p.1) [] = some (List.ofFn p.2.val)
      then _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up p.2) else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d =>
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w p.1) [] = some (List.ofFn p.2.val))) (by simp)
    (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A n d (ULift.up p.2))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
