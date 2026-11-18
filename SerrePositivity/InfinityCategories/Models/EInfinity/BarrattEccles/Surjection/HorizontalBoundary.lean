module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.InnerRowProjection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.FilterMapSelection
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.RowBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulBoundary

/-!
模型。文献の定義との比較は後で
# 固定内側置換の水平境界の外側非退化性

概要：Berger–Fresse §1.5.8 の水平移動で隣接選択語の外側境界が異なることを示す。
方針：境界の両文字が内側なら、同じ内側可用行の同じ共有末尾に一致する。
規約：内側置換を固定し、外側置換・除外状態・後続 table は任意。
使われ方：重複外側行を融合した復元表の出力の非退化性を得る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：同じ内側置換の隣接行の内側境界二文字は同じ値（BF §1.5.8）。
方針：前行の除外更新を内側へ射影し、同じ内側行の共有文字から再開する。
規約：前行は正で有効な長さ。境界二文字の内側射影が some であることを指定する。
使われ方：非退化な水平境界の両文字が同時に内側になることを排除する。 -/
lemma permutationComposition_horizontal_inner_boundary_eq {m n : ℕ}
    (σ σ' : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed : List (Fin (m + n))) (r : ℕ) (hr : 0 < r)
    (a b : Fin (m + n)) (c d : Fin n)
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm))[r - 1]? = some a)
    (hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take (r - 1))
      (List.ofFn (permutationComposition m n k σ' τ).symm)).head? = some b)
    (ha : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some c) (hb : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k b = some d) : a = b := by
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ' τ).symm)
  let prev := (xs.take (r - 1)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)
  obtain ⟨hi, hv⟩ := List.getElem?_eq_some_iff.mp he
  have hi' : r - 1 + 1 = r := by omega
  have hsplit : xs = xs.take (r - 1) ++ a :: xs.drop r := by
    have hd := List.getElem_cons_drop hi
    rw [hv, hi'] at hd
    change a :: xs.drop r = xs.drop (r - 1) at hd
    calc
      xs = xs.take (r - 1) ++ xs.drop (r - 1) := (List.take_append_drop _ _).symm
      _ = xs.take (r - 1) ++ a :: xs.drop r := by rw [← hd]
  have hav : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm) =
      xs.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_available_composition_row k σ τ removed).symm
  have hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)).take
      prev.length = prev := by
    rw [hav, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.filterMap_take_prefix]
  have hup : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (rem.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm) =
      (xs.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).drop prev.length := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available ((removed ++ xs.take (r - 1)).filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) _ = _
    rw [List.filterMap_append]
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) ++
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)).take prev.length)
          (List.ofFn τ.symm) := by rw [hp]
      _ = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)) (List.ofFn τ.symm)).drop prev.length :=
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available_after_take _ _ (List.nodup_ofFn_ofInjective τ.symm.injective) _
      _ = _ := by rw [hav]
  have hproject : ys.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k) =
      (xs.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).drop prev.length :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_available_composition_row k σ' τ rem).trans hup
  have hhead : (ys.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).head? = some d := by
    obtain ⟨tail, hy⟩ := List.head?_eq_some_iff.mp hh
    change ys = b :: tail at hy
    rw [hy, List.filterMap_cons, hb]
    rfl
  have hcomputed : (ys.filterMap (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k)).head? = some c := by
    rw [hproject, hsplit, List.filterMap_append, List.filterMap_cons, ha]
    rw [List.drop_left]
    rfl
  have hcd : c = d := Option.some.inj (hcomputed.symm.trans hhead)
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_partial_injective k a b c ha (hb.trans (congrArg some hcd.symm))

/-- 概要：同じ外側射影を持つ異なる二文字は両方が内側（BF §1.5.8）。
方針：挿入ラベルの直和分解で外側同士・内外・内側同士を区別する。
規約：等しい元の文字という場合も別の選択肢として残す。
使われ方：水平境界の外側射影が一致する場合を実際の内側境界へ戻す。 -/
lemma outerLabel_eq_cases {m n : ℕ} (k : Fin (m + 1)) (a b : Fin (m + n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k a = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b) :
    a = b ∨ ∃ c d, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some c ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k b = some d := by
  obtain ⟨x, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective a
  obtain ⟨y, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInsertionEquiv m n k).symm.surjective b
  cases x with
  | inl x =>
    cases y with
    | inl y =>
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, Equiv.apply_symm_apply] at h
      exact Or.inl (congrArg (remainingPosition m n k) (Subtype.ext h))
    | inr y =>
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, Equiv.apply_symm_apply] at h
      exact (x.property h).elim
  | inr x =>
    cases y with
    | inl y =>
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel, Equiv.apply_symm_apply] at h
      exact (y.property h.symm).elim
    | inr y => exact Or.inr ⟨x, y, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted k x, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_inserted k y⟩

/-- 概要：非退化な成功表の水平境界は外側へ戻しても異なる（BF §1.5.8）。
方針：外側値の一致を元の値の一致か内側二文字へ分け、両方を境界非退化性で排除する。
規約：同じ内側置換を持つ任意の二つの外側置換に適用する。
使われ方：圧縮した外側表の水平境界の非退化性を示す。 -/
lemma permutationComposition_horizontal_outer_boundary_ne {m n : ℕ}
    (σ σ' : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (k : Fin (m + 1)) (removed out : List (Fin (m + n)))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (a b : Fin (m + n))
    (he : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm))[r - 1]? = some a)
    (hh : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed
      (List.ofFn (permutationComposition m n k σ τ).symm)).take (r - 1))
      (List.ofFn (permutationComposition m n k σ' τ).symm)).head? = some b)
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ' τ).symm, s) :: rest)
      removed = some out) (hc : out.IsChain (· ≠ ·)) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k a ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.outerLabel k b := by
  have hne := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_boundary_ne _ _ r s rest removed out a b he hh h hc
  have hr := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h).1
  intro hlabel
  rcases _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.outerLabel_eq_cases k a b hlabel with heq | ⟨c, d, ha, hb'⟩
  · exact hne heq
  · exact hne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_horizontal_inner_boundary_eq σ σ' τ k removed r hr
      a b c d he hh ha hb')

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
