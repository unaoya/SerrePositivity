module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySuccessEquiv
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.DegreeZero
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroPaths
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleZeroDirections

/-!
模型。文献の定義との比較は後で
# nullary 次数零の全成功和と実際の部分合成

概要：Berger–Fresse §1.5.7–9 の空語合成で零項を含めた一般の TR 有限和を比較する。
方針：複数出現・退化項を零にし、成功項全単射の和を両線形部分合成へ戻す。
規約：任意の可換環と全外側次数、正の出力 arity。
使われ方：実際の nullary shuffle 合成の TR 保存を正規化鎖へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection _root_.SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]

/-- 概要：非零候補でない元の成功項の空語合成は零（BF §1.2.4・§1.5.7–9）。
方針：出現数が一以外なら分割なし、一なら削除語の退化性で正規化を零にする。
規約：係数環の非零性を要求しない。
使われ方：全成功語の和から nullary 非零候補の有限部分型へ制限する。 -/
lemma compositionOnWords_nullary_zero_of_not_source {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w) (hp : ¬ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount p.val.2.val k = 1 ∧
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn p.val.2.val)).IsChain (· ≠ ·))) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k = 0 := by
  by_cases hc : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount p.val.2.val k = 1
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords_nullary_of_count_eq_one A _ _ _ hc]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_eq_zero_of_not_isChain A _ (fun hn => hp ⟨hc, hn⟩)
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords_nullary_of_count_ne_one A _ _ _ hc

/-- 概要：全成功基底語の空語合成和は非零候補部分型の和（BF §1.5.7–9）。
方針：成功語を候補とその補集合に分け、補集合の全項を零にする。
規約：失敗・退化した元の表は成功語和に既に含まれない。
使われ方：成功全単射の和を元の onSequence の部分合成へ戻す。 -/
lemma sum_nullary_all_eq_source {m d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1)) :
    (∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k) =
      ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k := by
  classical
  let P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w → Prop := fun p => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.occurrenceCount p.val.2.val k = 1 ∧
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.eraseSlotWord k (List.ofFn p.val.2.val)).IsChain (· ≠ ·)
  let f : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.degreeModule A (m + 0) (d + 0) := fun p =>
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k
  have hz : (∑ p : {p // ¬ P p}, f p.val) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.compositionOnWords_nullary_zero_of_not_source A w k p.val p.property
  have hs := Fintype.sum_subtype_add_sum_subtype P f
  rw [hz] at hs
  have htypes : Subtype.fintype P = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.nullarySourceFintype w k := Subsingleton.elim _ _
  rw [htypes] at hs
  simpa only [add_zero] using hs.symm

/-- 概要：nullary 次数零の onSequence は空語の基底元（BF §0・§1.3.1）。
方針：既存の空語の正規化を ofFn と基底の等式へ移す。
規約：空集合の置換列は唯一だが任意の列として受ける。
使われ方：実際の空語入力の TR を両線形部分合成へ代入する。 -/
lemma onSequence_nullary_zero_basis (inner : Fin 1 → Equiv.Perm (Fin 0)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_zero]
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator A (List.ofFn (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))).val) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.listGenerator_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator_word]

/-- 概要：実際の指定値削除列の TR は元の TR と空語の部分合成（BF §1.5.7–9）。
方針：全成功基底和を全単射で移し、零項を戻して元の双線形合成を評価する。
規約：正の出力 arity と全次数、任意の可換環。
使われ方：唯一の次数零の内側 shuffle を含む一般の合成保存。 -/
lemma onSequence_nullary_composition_of_pos {m d : ℕ} (hm : 0 < m)
    (w : Fin (d + 1) → Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin 0))
    (k : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j => permutationComposition m 0 k (w j) τ) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d 0 k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A w)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))))) := by
  calc
    _ = ∑ q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord (fun j => permutationComposition m 0 k (w j) τ),
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (m + 0) (d + 0) (ULift.up q.val.2) :=
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_sum_successfulWords A hm _
    _ = ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.NullarySource w k,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_nullary_source_eq_target A hm w τ k).symm
    _ = ∑ p : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulWord w,
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionOnWords A p.val.2 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationWord (1 : Equiv.Perm (Fin 0))) k :=
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_nullary_all_eq_source A w k).symm
    _ = _ := by
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_eq_sum_successfulWords A (Nat.zero_lt_succ m) w]
      simp only [map_sum, LinearMap.sum_apply, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition_basis]

/-- 概要：内側空語の全 shuffle 和で TR は部分合成を保つ（BF §1.5.7–9）。
方針：唯一の垂直次数零の経路を評価し、実際の指定値削除列の一般公式を使う。
規約：外側次数は任意、出力 arity は正。
使われ方：nullary 次数零の正規化生成元と任意の鎖の合成保存。 -/
lemma onSequence_partialComposition_nullary_zero_of_pos {m d : ℕ} (hm : 0 < m)
    (k : Fin (m + 1)) (outer : Fin (d + 1) → Equiv.Perm (Fin (m + 1)))
    (inner : Fin 1 → Equiv.Perm (Fin 0)) :
    (∑ s : ShufflePath d 0, (s.sign : ℤ) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A (fun j =>
      permutationComposition m 0 k (outer (s.horizontal j)) (inner (s.vertical j)))) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.partialComposition A m 0 d 0 k (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A outer) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence A inner) := by
  let _ : Unique (ShufflePath d 0) :=
    ⟨⟨zeroRightPath d⟩, fun s => s.rightZero_unique (zeroRightPath d)⟩
  simp only [Fintype.sum_unique, ShufflePath.sign_rightZero, Units.val_one, one_smul,
    ShufflePath.horizontal_rightZero, Fin.eq_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_zero_basis]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.onSequence_nullary_composition_of_pos A hm outer (inner 0) k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
