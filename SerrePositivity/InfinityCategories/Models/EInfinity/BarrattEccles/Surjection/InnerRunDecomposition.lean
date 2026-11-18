module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.OuterTableRecovery
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapseSeparated

/-!
模型。文献の定義との比較は後で
# 格子方向に進む合成表の水平区間分割

概要：Berger–Fresse §1.5.8 の内側表の逆構成に必要な実際の水平区間を切り出す。
方針：同じ内側置換の段を先頭区間へ加え、変わる段では共通外側置換の垂直辺で切る。
規約：各区間は最後の一行を明示し、その前の水平歩数は零でもよい。
使われ方：各水平区間の内側一行への復元を、実際の全表で反復する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

/-- 概要：実際の合成表を垂直辺で区切った非空な水平区間列（BF §1.5.8）。
方針：各区間の最後の行と次の区間の最初の行で外側置換を共有させる。
規約：区間の内側置換列には隣接重複がなく、元の行長は全て保持する。
使われ方：実際の成功表の内側抽出を状態を合わせて復元するための分割証明書。 -/
inductive InnerRunDecomposition {m n : ℕ} :
    List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ) →
      List (Equiv.Perm (Fin n)) → Prop
  | single (τ : Equiv.Perm (Fin n)) (before : List (Equiv.Perm (Fin (m + 1)) × ℕ))
      (σ : Equiv.Perm (Fin (m + 1))) (r : ℕ) :
      InnerRunDecomposition (before.map (fun p => (p.1, τ, p.2)) ++ [(σ, τ, r)]) [τ]
  | step (τ τ' : Equiv.Perm (Fin n)) (hne : τ ≠ τ')
      (before : List (Equiv.Perm (Fin (m + 1)) × ℕ))
      (σ : Equiv.Perm (Fin (m + 1))) (r s : ℕ)
      (rest : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
      (sources : List (Equiv.Perm (Fin n)))
      (tail : InnerRunDecomposition ((σ, τ', s) :: rest) (τ' :: sources)) :
      InnerRunDecomposition
        (before.map (fun p => (p.1, τ, p.2)) ++ (σ, τ, r) :: (σ, τ', s) :: rest)
        (τ :: τ' :: sources)

/-- 概要：同じ内側置換の行は最初の水平区間へ加えられる（BF §1.5.8）。
方針：分割の最初の区間の before に一行を付ける。
規約：先行行の外側置換と行長は任意。
使われ方：全表の行で帰納して水平区間分割を構成する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.prepend {m n : ℕ}
    {entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ)}
    {τ : Equiv.Perm (Fin n)} {sources : List (Equiv.Perm (Fin n))}
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition entries (τ :: sources))
    (σ : Equiv.Perm (Fin (m + 1))) (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition ((σ, τ, r) :: entries) (τ :: sources) := by
  cases h with
  | single τ before σlast s =>
    simpa only [List.map_cons, List.cons_append] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.single τ ((σ, r) :: before) σlast s
  | step τ τ' hne before σlast s t rest sources ht =>
    simpa only [List.map_cons, List.cons_append] using
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.step τ τ' hne ((σ, r) :: before) σlast s t rest sources ht

/-- 概要：隣接する内外の一方が固定された任意の非空表は水平区間に分解できる（BF §1.5.8）。
方針：後続を分解し、同じ内側なら区間へ加え、異なるなら外側の一致で垂直辺を作る。
規約：成功や非退化性をまだ要求せず、実際の置換と行長の列だけで構成する。
使われ方：shuffle 経路の軸方向条件から具体的な成分切り出しを供給する。 -/
lemma innerRunDecomposition_exists {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (r : ℕ)
    (rest : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ))
    (haxis : ((σ, τ, r) :: rest).IsChain (fun p q => p.1 = q.1 ∨ p.2.1 = q.2.1)) :
    ∃ sources, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition ((σ, τ, r) :: rest) (τ :: sources) := by
  induction rest generalizing σ τ r with
  | nil => exact ⟨[], .single τ [] σ r⟩
  | cons entry rest ih =>
    obtain ⟨σ', τ', s⟩ := entry
    obtain ⟨sources, ht⟩ := ih σ' τ' s haxis.tail
    by_cases he : τ = τ'
    · subst τ'
      exact ⟨sources, ht.prepend σ r⟩
    · have hs : σ = σ' := ((List.isChain_cons_cons.mp haxis).1).resolve_right he
      subst σ'
      exact ⟨τ' :: sources, .step τ τ' he [] σ r s rest sources ht⟩

/-- 概要：水平区間の元の組の列から実際の固定内側行列を得る（BF §1.5.8）。
方針：二つの map の合成を実際の合成逆置換行で評価する。
規約：行長を変更しない。
使われ方：区間分割の先行部分を horizontal_inner_consumption に渡す。 -/
lemma mixedTable_horizontal {m n : ℕ} (k : Fin (m + 1)) (τ : Equiv.Perm (Fin n))
    (before : List (Equiv.Perm (Fin (m + 1)) × ℕ)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable k (before.map (fun p => (p.1, τ, p.2))) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k before := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.mixedTable, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_map, Function.comp_def]

private lemma collapse_constant_map_cons {α β : Type*} [DecidableEq β]
    (before : List α) (b : β) (post : List β) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (before.map (fun _ => b) ++ b :: post) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (b :: post) := by
  induction before with
  | nil => rfl
  | cons a before ih =>
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend b
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (before.map (fun _ => b) ++ b :: post)) = _
    rw [ih]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend_idempotent b (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse post)

/-- 概要：分割の内側置換列は実際の元の内側列の連続重複縮約（BF §1.5.8）。
方針：各水平区間の定数列を一文字へ縮め、垂直境界の異なる置換を保持する。
規約：分割証明書の選び方にかかわらず、元の列だけから内側列が決まる。
使われ方：復元した内側行列を元の内側次数の実際の行列へ同定する。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition.sources_eq {m n : ℕ}
    {entries : List (Equiv.Perm (Fin (m + 1)) × Equiv.Perm (Fin n) × ℕ)}
    {sources : List (Equiv.Perm (Fin n))} (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InnerRunDecomposition entries sources) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (entries.map (fun p => p.2.1)) = sources := by
  induction h with
  | single τ before σ r =>
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons, List.map_nil]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_constant_map_cons]
    rfl
  | step τ τ' hne before σ r s rest sources ht ih =>
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.collapse_constant_map_cons]
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend τ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.collapse (((σ, τ', s) :: rest).map (fun p => p.2.1))) = _
    rw [ih, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.AdjacentCollapse.prepend, ite_eq_right hne]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
