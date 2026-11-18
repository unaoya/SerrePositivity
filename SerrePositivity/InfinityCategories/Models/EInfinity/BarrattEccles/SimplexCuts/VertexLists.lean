module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TerminalCoordinates
public import Mathlib.Data.List.OfFn

/-!
模型。文献の定義との比較は後で
# 色ごとの頂点列

Berger–Fresse §2.2.6–7、M14 L09a R02。
非全射の色付けも許し、欠けた色を空のリストで表す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts

/-- 昇順に並べた色のfiberを、垂直座標へ写す。 -/
def verticesList {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (v : Fin (m + 1) → Fin r) (c : Fin r) :
    List (Fin (q + 1)) :=
  ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s v c).sort (· ≤ ·)).map (fun i => s.vertical i)

/-- R02で使う接頭部の色付け。全射性は要求しない。 -/
def prefixLabels {m r : ℕ} (v : Fin (m + 1) → Fin r) (p : Fin (m + 1)) :
    Fin (p.val + 1) → Fin r := fun i => v ⟨i.val, by have hi := i.isLt; omega⟩

/-- 最後の垂直辺の後に色cが現れる回数。 -/
def terminalMultiplicity {m r : ℕ} (v : Fin (m + 1) → Fin r)
    (p : Fin (m + 1)) (c : Fin r) : ℕ :=
  (Finset.univ.filter (fun i => p ≤ i ∧ v i = c)).card

/-- L09a C02：有限順序のfiberの昇順列は、全順序列をfilterして得られる。 -/
lemma sort_filter_univ (N : ℕ) (P : Fin N → Prop) [DecidablePred P] :
    (Finset.univ.filter P).sort (· ≤ ·) = (List.finRange N).filter (fun i => decide (P i)) := by
  let l := (List.finRange N).filter (fun i => decide (P i))
  have ht : l.toFinset = Finset.univ.filter P := by
    ext i
    simp [l]
  rw [← ht]
  apply (List.toFinset_sort _ (List.nodup_finRange N |>.filter _)).mpr
  have h := (Finset.pairwise_sort (Finset.univ : Finset (Fin N)) (· ≤ ·)).filter
    (fun i => decide (P i))
  simpa only [Fin.sort_univ] using h

/-- 頂点の列から一つの色の値を読むリスト操作。 -/
def selectColor {r : ℕ} {β : Type*} (c : Fin r) (l : List (Fin r × β)) : List β :=
  (l.filter (fun x => x.1 == c)).map Prod.snd

/-- R02の証明分割：色のfiberの定義を、全頂点の列へ書き直す。 -/
lemma verticesList_eq_selectColor {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q)
    (v : Fin (m + 1) → Fin r) (c : Fin r) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList s v c =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (List.ofFn (fun i => (v (s.horizontal i), s.vertical i))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.verticesList _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sort_filter_univ]
  rw [List.ofFn_comp' (fun i => i) (fun i => (v (s.horizontal i), s.vertical i))]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor, List.filter_map, List.map_map]
  rfl

/-- R02の証明分割：色の取り出しは連結と可換。 -/
lemma selectColor_append {r : ℕ} {β : Type*} (c : Fin r) (l l' : List (Fin r × β)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (l ++ l') = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l ++ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l' := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor, List.filter_append, List.map_append]

/-- R02の証明分割：垂直座標だけの写像は色の取り出しと可換。 -/
lemma selectColor_map {r : ℕ} {β γ : Type*} (c : Fin r) (f : β → γ)
    (l : List (Fin r × β)) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c (l.map (fun x => (x.1, f x.2))) = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor c l).map f := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.selectColor, List.filter_map, List.map_map]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
