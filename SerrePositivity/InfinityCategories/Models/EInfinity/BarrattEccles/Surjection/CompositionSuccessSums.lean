module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccessEquiv
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ListDegeneracy

/-!
模型。文献の定義との比較は後で
# 全実際の shuffle 項と元の成功二表の符号付き有限和

概要：Berger–Fresse §1.5.6–9 の正の内側 arity の全単射を全有限和へ適用する。
方針：失敗・退化出力の零項を除き、成功項の全単射と経路符号一致で添字を変更する。
規約：任意の可換環。零でない係数を仮定しない。
使われ方：TR の一般の部分合成保存を元の二つの TR 有限和へ帰着する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：実際の経路・Schedule の符号付き TR 項（BF §1.5.6）。
方針：既存の shuffle 符号を実際の合成置換列の table 項へ作用させる。
規約：失敗・退化出力項もこの定義では保持する。
使われ方：全経路と全 Schedule の有限和の被加数。 -/
def signedTerm {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (p : ShufflePath d e × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) :=
  (p.1.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => permutationComposition m n k (outer (p.1.horizontal j))
    (inner (p.1.vertical j))) p.2

/-- 概要：元の成功二表と分割の符号付き合成項（BF §1.5.6）。
方針：既存の compositionSign と実際の合成語の生成元を使う。
規約：添字は元の両置換列を固定した実際の成功データ。
使われ方：成功項の全単射で得られる元の側の有限和の被加数。 -/
def sourceTerm {m n d e : ℕ}
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + n) (d + e) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionSign c.val.outerWord c.val.innerWord c.val.slot c.val.cuts •
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A c.val.outerWord c.val.innerWord c.val.slot c.val.cuts

/-- 概要：成功項の全単射は各項とその符号を保つ（BF §1.5.6–9）。
方針：正方向の実際の抽出成功を term で評価し、既存の経路符号一致を使う。
規約：任意の可換環上。
使われ方：全成功項の有限和の添字変更で被加数を一致させる。 -/
lemma forward_term {m n d e : ℕ} (hn : 0 < n)
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn c).val = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c := by
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => permutationComposition m n k
      (outer ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn c).val.1.horizontal j))
      (inner ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn c).val.1.vertical j))) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn c).val.2 =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeGenerator A c.val.outerWord c.val.innerWord c.val.slot c.val.cuts := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.source_success c]
    rfl
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm
  rw [ht]
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts).sign : ℤ) • _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath_sign]
  rfl

/-- 概要：全非退化成功経路項の符号付き有限和は元の成功二表＋分割の和（BF §1.5.6–9）。
方針：構成した有限な成功項全単射で添字を変更し、各項の符号一致を適用する。
規約：元データの Fintype は全単射から構成したものを局所的に選ぶ。
使われ方：失敗・退化の零項を除いた全合成和の一致。 -/
lemma sum_target_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
    (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k p.val) =
      ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  symm
  apply Fintype.sum_equiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.equiv hn outer inner k)
  intro c
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward_term A hn c).symm

/-- 概要：非退化成功に属さない実際の経路項は零（BF §1.5.6–9）。
方針：抽出失敗なら定義で零、成功なら非退化性の否定から正規化を零へ送る。
規約：係数環や内側 arity に非零性・正値性を要求しない。
使われ方：全経路と全 Schedule の有限和へ成功項の対応を戻す。 -/
lemma signedTerm_eq_zero_of_not_successful {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (p : ShufflePath d e × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) (hp : ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Successful outer inner k p) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k p = 0 := by
  have ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term A (fun j => permutationComposition m n k (outer (p.1.horizontal j))
      (inner (p.1.vertical j))) p.2 = 0 := by
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.term
    cases h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (p.1.horizontal j))
      (inner (p.1.vertical j))) p.2) [] with
    | none => rfl
    | some out =>
      have hc : ¬ out.IsChain (· ≠ ·) := fun hc => hp ⟨out, h, hc⟩
      simp only [Option.map_some, Option.getD_some]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_eq_zero_of_not_isChain A out hc
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm, ht, smul_zero]

/-- 概要：失敗と退化を含む全実際の経路・Schedule の和は元の成功二表＋分割の和（BF §1.5.6–9）。
方針：有限な直積を成功と非成功に分け、非成功和を零にして成功項全単射を適用する。
規約：正の内側 arity。元データの有限型は構成済み全単射から選ぶ。
使われ方：全ての shuffle と TR Schedule を含む一般の合成保存の左辺。 -/
lemma sum_all_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
    (∑ p : ShufflePath d e × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k p) =
      ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c := by
  classical
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  have hz : (∑ p : {p // ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Successful outer inner k p}, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm_eq_zero_of_not_successful A outer inner k p.val p.property
  have hs := Fintype.sum_subtype_add_sum_subtype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Successful outer inner k)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k)
  rw [hz, add_zero] at hs
  have htypes : Subtype.fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Successful outer inner k) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.targetFintype outer inner k :=
    Subsingleton.elim _ _
  rw [htypes] at hs
  exact hs.symm.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sum_target_eq_source A hn outer inner k)

/-- 概要：全 shuffle 符号付き onSequence の和は元の成功二表と分割の有限和（BF §1.5.6–9）。
方針：正の合成 arity の onSequence を全 Schedule の和へ展開し、全直積和の一致を使う。
規約：任意の可換環。失敗・退化項は既に零として含まれる。
使われ方：実際の BE の shuffle 合成の TR を元の成功二表の和へ戻す。 -/
lemma sum_onSequence_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
    (∑ s : ShufflePath d e, (s.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j =>
      permutationComposition m n k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      ∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceTerm A c := by
  let _ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sourceFintype hn outer inner k
  have hN : m + n ≠ 0 := by omega
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence, ite_eq_right hN, Finset.smul_sum]
  change (∑ s : ShufflePath d e, ∑ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.signedTerm A outer inner k (s, r)) = _
  rw [← Fintype.sum_prod_type]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.sum_all_eq_source A hn outer inner k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess
