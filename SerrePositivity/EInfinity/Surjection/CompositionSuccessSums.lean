module

public import SerrePositivity.EInfinity.Surjection.CompositionSuccessEquiv
public import SerrePositivity.EInfinity.Surjection.ListDegeneracy

/-!
# 全実際の shuffle 項と元の成功二表の符号付き有限和

概要：Berger–Fresse §1.5.6–9 の正の内側 arity の全単射を全有限和へ適用する。
方針：失敗・退化出力の零項を除き、成功項の全単射と経路符号一致で添字を変更する。
規約：任意の可換環。零でない係数を仮定しない。
使われ方：TR の一般の部分合成保存を元の二つの TR 有限和へ帰着する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.Surjection.CompositionSuccess

open BarrattEccles TableReduction

variable (A : Type u) [CommRing A]

/-- 概要：実際の経路・Schedule の符号付き TR 項（BF §1.5.6）。
方針：既存の shuffle 符号を実際の合成置換列の table 項へ作用させる。
規約：失敗・退化出力項もこの定義では保持する。
使われ方：全経路と全 Schedule の有限和の被加数。 -/
def signedTerm {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (p : ShufflePath d e × Schedule (m + n) (d + e)) : degreeModule A (m + n) (d + e) :=
  (p.1.sign : ℤ) • term A (fun j => permutationComposition m n k (outer (p.1.horizontal j))
    (inner (p.1.vertical j))) p.2

/-- 概要：元の成功二表と分割の符号付き合成項（BF §1.5.6）。
方針：既存の compositionSign と実際の合成語の生成元を使う。
規約：添字は元の両置換列を固定した実際の成功データ。
使われ方：成功項の全単射で得られる元の側の有限和の被加数。 -/
def sourceTerm {m n d e : ℕ}
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)}
    (c : Source outer inner k) : degreeModule A (m + n) (d + e) :=
  compositionSign c.val.outerWord c.val.innerWord c.val.slot c.val.cuts •
    compositeGenerator A c.val.outerWord c.val.innerWord c.val.slot c.val.cuts

/-- 概要：成功項の全単射は各項とその符号を保つ（BF §1.5.6–9）。
方針：正方向の実際の抽出成功を term で評価し、既存の経路符号一致を使う。
規約：任意の可換環上。
使われ方：全成功項の有限和の添字変更で被加数を一致させる。 -/
lemma forward_term {m n d e : ℕ} (hn : 0 < n)
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)} (c : Source outer inner k) :
    signedTerm A outer inner k (forward hn c).val = sourceTerm A c := by
  have ht : term A (fun j => permutationComposition m n k
      (outer ((forward hn c).val.1.horizontal j))
      (inner ((forward hn c).val.1.vertical j))) (forward hn c).val.2 =
      compositeGenerator A c.val.outerWord c.val.innerWord c.val.slot c.val.cuts := by
    dsimp only [forward]
    rw [term, source_success c]
    rfl
  unfold signedTerm
  rw [ht]
  change ((compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts).sign : ℤ) • _ = _
  rw [compositionPath_sign]
  rfl

/-- 概要：全非退化成功経路項の符号付き有限和は元の成功二表＋分割の和（BF §1.5.6–9）。
方針：構成した有限な成功項全単射で添字を変更し、各項の符号一致を適用する。
規約：元データの Fintype は全単射から構成したものを局所的に選ぶ。
使われ方：失敗・退化の零項を除いた全合成和の一致。 -/
lemma sum_target_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := sourceFintype hn outer inner k
    (∑ p : Target outer inner k, signedTerm A outer inner k p.val) =
      ∑ c : Source outer inner k, sourceTerm A c := by
  let _ := sourceFintype hn outer inner k
  symm
  apply Fintype.sum_equiv (equiv hn outer inner k)
  intro c
  exact (forward_term A hn c).symm

/-- 概要：非退化成功に属さない実際の経路項は零（BF §1.5.6–9）。
方針：抽出失敗なら定義で零、成功なら非退化性の否定から正規化を零へ送る。
規約：係数環や内側 arity に非零性・正値性を要求しない。
使われ方：全経路と全 Schedule の有限和へ成功項の対応を戻す。 -/
lemma signedTerm_eq_zero_of_not_successful {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (p : ShufflePath d e × Schedule (m + n) (d + e)) (hp : ¬ Successful outer inner k p) :
    signedTerm A outer inner k p = 0 := by
  have ht : term A (fun j => permutationComposition m n k (outer (p.1.horizontal j))
      (inner (p.1.vertical j))) p.2 = 0 := by
    unfold term
    cases h : reduceRows (rows (fun j => permutationComposition m n k (outer (p.1.horizontal j))
      (inner (p.1.vertical j))) p.2) [] with
    | none => rfl
    | some out =>
      have hc : ¬ out.IsChain (· ≠ ·) := fun hc => hp ⟨out, h, hc⟩
      simp only [Option.map_some, Option.getD_some]
      exact listGenerator_eq_zero_of_not_isChain A out hc
  simp only [signedTerm, ht, smul_zero]

/-- 概要：失敗と退化を含む全実際の経路・Schedule の和は元の成功二表＋分割の和（BF §1.5.6–9）。
方針：有限な直積を成功と非成功に分け、非成功和を零にして成功項全単射を適用する。
規約：正の内側 arity。元データの有限型は構成済み全単射から選ぶ。
使われ方：全ての shuffle と TR Schedule を含む一般の合成保存の左辺。 -/
lemma sum_all_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := sourceFintype hn outer inner k
    (∑ p : ShufflePath d e × Schedule (m + n) (d + e), signedTerm A outer inner k p) =
      ∑ c : Source outer inner k, sourceTerm A c := by
  classical
  let _ := sourceFintype hn outer inner k
  have hz : (∑ p : {p // ¬ Successful outer inner k p}, signedTerm A outer inner k p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact signedTerm_eq_zero_of_not_successful A outer inner k p.val p.property
  have hs := Fintype.sum_subtype_add_sum_subtype (Successful outer inner k)
    (signedTerm A outer inner k)
  rw [hz, add_zero] at hs
  have htypes : Subtype.fintype (Successful outer inner k) = targetFintype outer inner k :=
    Subsingleton.elim _ _
  rw [htypes] at hs
  exact hs.symm.trans (sum_target_eq_source A hn outer inner k)

/-- 概要：全 shuffle 符号付き onSequence の和は元の成功二表と分割の有限和（BF §1.5.6–9）。
方針：正の合成 arity の onSequence を全 Schedule の和へ展開し、全直積和の一致を使う。
規約：任意の可換環。失敗・退化項は既に零として含まれる。
使われ方：実際の BE の shuffle 合成の TR を元の成功二表の和へ戻す。 -/
lemma sum_onSequence_eq_source {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    letI := sourceFintype hn outer inner k
    (∑ s : ShufflePath d e, (s.sign : ℤ) • onSequence A (fun j =>
      permutationComposition m n k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      ∑ c : Source outer inner k, sourceTerm A c := by
  let _ := sourceFintype hn outer inner k
  have hN : m + n ≠ 0 := by omega
  simp only [onSequence, ite_eq_right hN, Finset.smul_sum]
  change (∑ s : ShufflePath d e, ∑ r : Schedule (m + n) (d + e),
    signedTerm A outer inner k (s, r)) = _
  rw [← Fintype.sum_prod_type]
  exact sum_all_eq_source A hn outer inner k

end SerrePositivity.EInfinity.Surjection.CompositionSuccess
