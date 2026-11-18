module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.ShuffleReconstruction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeBasis

/-!
模型。文献の定義との比較は後で
# 元の二つの成功表と実際の非退化 shuffle 成功項の全単射

概要：Berger–Fresse §1.5.6–9 の正の内側 arity の全成功項を実際の有限な添字で対応させる。
方針：固定した置換列と挿入位置の入力データを経路・Schedule へ送り、一意な逆構成を使う。
規約：入力データに元の成功を含み、出力側には実際の成功と非退化性を含む。
使われ方：一般の TR の合成保存で符号付き有限和を添字変更する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：元の両置換列と挿入位置を固定した成功二表と分割（BF §1.5.6–9）。
方針：既存 TableCompositionData の元の置換列と位置だけを部分型で固定する。
規約：語・Schedule・分割は成功条件を満たす全ての値を動く。
使われ方：合成保存の元の二つの TR 項と分割の和の添字。 -/
abbrev Source {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :=
  {c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableCompositionData m n d e // c.outer = outer ∧ c.inner = inner ∧ c.slot = k}

/-- 概要：経路と Schedule が実際に非退化出力の抽出に成功する条件（BF §1.5.6–9）。
方針：経路の各頂点の置換部分合成で作る全表の成功を直接要求する。
規約：失敗項と退化出力項は含めない。
使われ方：全有限和のうち零でない候補項を選び出す。 -/
def Successful {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (p : ShufflePath d e × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e)) : Prop :=
  ∃ out, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (p.1.horizontal j))
    (inner (p.1.vertical j))) p.2) [] = some out ∧ out.IsChain (· ≠ ·)

/-- 概要：実際の非退化成功を持つ経路・Schedule の有限な部分型（BF §1.5.6–9）。
方針：全経路と全 Schedule の有限な直積を成功条件で制限する。
規約：出力語自体は成功から一意に決まり添字に追加しない。
使われ方：元の成功二表と分割に対応する出力側の和の添字。 -/
abbrev Target {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :=
  {p : ShufflePath d e × _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule (m + n) (d + e) // _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Successful outer inner k p}

/-- 概要：成功した経路・Schedule の添字は有限（BF §1.5.6–9）。
方針：有限な直積の部分型の有限性から Fintype を選ぶ。
規約：成功条件の計算可能性を追加仮定にしない。
使われ方：全非退化成功項の実際の有限和。 -/
noncomputable instance targetFintype {m n d e : ℕ}
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k) := Fintype.ofFinite _

/-- 概要：固定した元の置換列で正方向の経路・Schedule は元の合成語の抽出に成功（BF §1.5.7）。
方針：固定条件で pathSequence の各頂点を元の実際の置換列へ戻す。
規約：経路と Schedule は既存の正方向構成そのもの。
使われ方：成功二表を実際の非退化成功項へ送る写像。 -/
lemma source_success {m n d e : ℕ}
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)} (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) :
    let s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (s.horizontal j))
      (inner (s.vertical j))) c.val.fusedSchedule) [] =
        some (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord c.val.outerWord c.val.innerWord c.val.slot c.val.cuts) := by
  let s := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts
  have hw : c.val.pathSequence = fun j => permutationComposition m n k
      (outer (s.horizontal j)) (inner (s.vertical j)) := by
    funext j
    change permutationComposition m n c.val.slot (c.val.outer (s.horizontal j))
      (c.val.inner (s.vertical j)) = _
    rw [c.property.1, c.property.2.1, c.property.2.2]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (fun j => permutationComposition m n k (outer (s.horizontal j))
    (inner (s.vertical j))) c.val.fusedSchedule) [] = _
  rw [← hw]
  exact c.val.pathSequence_success

/-- 概要：成功二表と分割を実際の非退化成功経路項へ送る（BF §1.5.6–9）。
方針：compositionPath・fusedSchedule と正方向成功・合成語非退化性を組にする。
規約：内側 arity は正。
使われ方：全成功項の全単射の正方向。 -/
def forward {m n d e : ℕ} (hn : 0 < n)
    {outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1))}
    {inner : Fin (e + 1) → Equiv.Perm (Fin n)} {k : Fin (m + 1)}
    (c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts, c.val.fusedSchedule),
    _, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.source_success c, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositeWord_isChain _ _ _ _ hn⟩

/-- 概要：正方向の成功項写像は単射（BF §1.5.9）。
方針：同じ経路・Schedule の実際の抽出出力を揃え、元データの一意性を使う。
規約：同じ元の両置換列と挿入位置を固定する。
使われ方：有限和の添字変更で項が重複しないことを保証する。 -/
lemma forward_injective {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn (outer := outer) (inner := inner) (k := k)) := by
  intro c c' he
  have hp := congrArg (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k => p.val.1) he
  have hr := congrArg (fun p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k => p.val.2) he
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c.val.outerWord c.val.innerWord c.val.slot c.val.cuts =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionPath c'.val.outerWord c'.val.innerWord c'.val.slot c'.val.cuts at hp
  change c.val.fusedSchedule = c'.val.fusedSchedule at hr
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.source_success c
  have hc' := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.source_success c'
  rw [← hp, ← hr] at hc'
  have hout := Option.some.inj (hc.symm.trans hc')
  apply Subtype.ext
  exact c.val.eq_of_same_output c'.val (c.property.1.trans c'.property.1.symm)
    (c.property.2.1.trans c'.property.2.1.symm) (c.property.2.2.trans c'.property.2.2.symm) hout

/-- 概要：実際の全非退化成功経路項は元の成功二表と分割から来る（BF §1.5.8）。
方針：一意な逆構成を適用し、元の経路・Schedule の往復を使う。
規約：元の成功二表・語・分割は入力に要求しない。
使われ方：有限和の添字変更で全ての非退化成功項を尽くす。 -/
lemma forward_surjective {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn (outer := outer) (inner := inner) (k := k)) := by
  intro p
  obtain ⟨out, h, hc⟩ := p.property
  obtain ⟨c, hsrc, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.shuffle_reconstruction_existsUnique hn k p.val.1 outer inner
    p.val.2 out h hc
  let src : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k := ⟨c, hsrc.1, hsrc.2.1, hsrc.2.2.1⟩
  refine ⟨src, ?_⟩
  apply Subtype.ext
  exact Prod.ext hsrc.2.2.2.1 hsrc.2.2.2.2.1

/-- 概要：元の成功二表＋分割と全実際の非退化成功項の全単射（BF §1.5.6–9）。
方針：正方向の単射と逆構成による全射から既存写像の同値を作る。
規約：内側 arity は正。
使われ方：全符号付き有限和の添字変更。 -/
def equiv {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k ≃ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward hn)
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward_injective hn outer inner k, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.forward_surjective hn outer inner k⟩

/-- 概要：元の全成功二表と分割の添字も有限（BF §1.5.6–9）。
方針：実際の有限な成功経路項との全単射で有限型構造を移す。
規約：成功二表を仮定した有限型は追加せず、構成した全単射から得る。
使われ方：元の全成功二表と分割の有限和を実際に記述する。 -/
@[instance_reducible] def sourceFintype {m n d e : ℕ} (hn : 0 < n)
    (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin (e + 1) → Equiv.Perm (Fin n)) (k : Fin (m + 1)) :
    Fintype (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Source outer inner k) :=
  Fintype.ofEquiv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.Target outer inner k) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess.equiv hn outer inner k).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionSuccess
