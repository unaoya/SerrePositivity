module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoslicePinchedLeft
public import Mathlib.Data.Finset.Max

/-!
概要：包含順序の path から最後の終点直前の頂点を取り出す。
方針：最終頂点を除いた有限集合の最大元を取り、包含と前半の合成に対する整合性を示す。
規約：Mathlib は包含順序なので最大元は単調。Kerodon の逆包含規約から向きを調整する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Remark 4.6.7.9（Tag 01LH）、右 pinched 模型への豊穣 Hom の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：最後の頂点へ至る path の最後の頂点以外の点の有限集合。
方針：Fin(n+1) の頂点が path に属する条件で全体を絞る。
規約：最初の端点 i は必ずこの集合に属する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD） の包含順序での右模型の座標。 -/
noncomputable def pathBeforeLast {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j ↦ ULift.up j.castSucc ∈ P.I)

/-- 概要：最後の頂点以外の path の点の集合は空でない。
方針：始点の所属を用いる。
規約：始点は最後の頂点とは異なる。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、最大元の定義の存在条件。 -/
lemma pathBeforeLast_nonempty {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : (pathBeforeLast P).Nonempty := by
  classical
  exact ⟨i, by simp [pathBeforeLast, P.left]⟩

/-- 概要：path の最後の頂点の直前の最大の点。
方針：最後の頂点を除いた有限集合の最大元を取る。
規約：値は Fin(n+1) で、元の添字を保持する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Mathlib の包含方向に合う右模型の比較。 -/
noncomputable def pathLastMaximum {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : Fin (n + 1) :=
  (pathBeforeLast P).max' (pathBeforeLast_nonempty P)

/-- 概要：path の最大の前終点は元の path に属する。
方針：有限集合の最大元の所属を使う。
規約：元の順序集合では castSucc で頂点を戻す。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、豊穣 Hom の単体の評価。 -/
lemma pathLastMaximum_mem {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : ULift.up (pathLastMaximum P).castSucc ∈ P.I := by
  classical
  have h := Finset.max'_mem (pathBeforeLast P) (pathBeforeLast_nonempty P)
  exact (Finset.mem_filter.mp h).2

/-- 概要：最後の頂点以外の path の各点は最大の前終点以下。
方針：有限集合の最大元の上界性を使う。
規約：点 j は Fin(n+1) で指定する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、包含と合成に対する整合性。 -/
lemma le_pathLastMaximum {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (j : Fin (n + 1))
    (hj : ULift.up j.castSucc ∈ P.I) : j ≤ pathLastMaximum P := by
  classical
  apply Finset.le_max'
  simp only [pathBeforeLast, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj

/-- 概要：path の包含は最大の前終点を増加させる。
方針：小さい path の最大元の所属を包含で写し、大きい path の上界性を使う。
規約：Mathlib の path の射は包含方向。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、最大元による nerve の射の関手性。 -/
lemma pathLastMaximum_mono {n : ℕ} {i : Fin (n + 1)}
    {P Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))} (h : P.I ⊆ Q.I) :
    pathLastMaximum P ≤ pathLastMaximum Q :=
  le_pathLastMaximum Q _ (h (pathLastMaximum_mem P))

/-- 概要：path の前半を合成しても最大の前終点は後半のものと同じ。
方針：前半の点は切断点以下であり、切断点は後半の最大元以下である。
規約：切断点 j は最後の頂点より前に置く。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の豊穣関手の合成則。 -/
lemma pathLastMaximum_comp {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (Q : Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    pathLastMaximum (@CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2))))
      _ ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ P Q) =
        pathLastMaximum Q := by
  let R : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) :=
    @CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
      ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ P Q
  change pathLastMaximum R = pathLastMaximum Q
  apply le_antisymm
  · have hm := pathLastMaximum_mem R
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · have hle := P.le_right _ hm
      change (pathLastMaximum R).castSucc ≤ j.castSucc at hle
      exact (Fin.castSucc_le_castSucc_iff.mp hle).trans (le_pathLastMaximum Q j Q.left)
    · exact le_pathLastMaximum Q _ hm
  · apply le_pathLastMaximum R
    exact Or.inr (pathLastMaximum_mem Q)

/-- 概要：path の最大の前終点を選ぶ関手。
方針：対象を最大元、包含をその単調性の順序射に写す。
規約：値域を ULift して Hom の単体集合の宇宙に揃える。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、豊穣 Hom の比較に使う座標射。 -/
noncomputable def pathLastMaximumFunctor {n : ℕ} (i : Fin (n + 1)) :
    Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) ⥤ ULift.{u} (Fin (n + 1)) where
  obj P := ULift.up (pathLastMaximum P)
  map f := homOfLE (pathLastMaximum_mono f.1.1.1)

/-- 概要：path の最大の前終点を取る標準単体への射。
方針：最大元を選ぶ関手の nerve と標準単体の nerve 表示の逆を合成する。
規約：始域の頂点は i、終点は追加した最後の頂点。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、右 pinched 比較の Hom 上の射。 -/
noncomputable def pathLastMaximumMap {n : ℕ} (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ (Δ[n] : SSet.{u}) :=
  nerveMap (pathLastMaximumFunctor i) ≫ (stdSimplex.isoNerve n).inv

/-- 概要：最後の頂点を固定した添字写像で path を写す。
方針：元の path の部分集合の像を取り、両端点は延長写像の計算で確認する。
規約：元の始点 i は α(i) に、追加した最後の頂点は最後の頂点に写る。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較写像の単体的な自然性。 -/
def pathLastReindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) {i : Fin (m + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1)))) :
    Path (ULift.up (α.toOrderHom i).castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := (fun k : ULift.{u} (Fin (m + 2)) ↦
    ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom k.down)) '' P.I
  left := ⟨ULift.up i.castSucc, P.left, by
    exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _)⟩
  right := ⟨ULift.up (Fin.last (m + 1)), P.right, by
    exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last _)⟩
  left_le k hk := by
    rcases hk with ⟨l, hl, rfl⟩
    change (α.toOrderHom i).castSucc ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom l.down
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom).monotone (P.left_le l hl)
  le_right k _ := Fin.le_last k.down

/-- 概要：path の最大の前終点を取る操作は最後の頂点固定の添字写像に自然。
方針：最大元の像の所属で一方の不等式を示し、像の最大元の原像で逆を示す。
規約：α は面・退化を含む任意の単体圏の射。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、右 pinched 比較の全次数の自然性。 -/
lemma pathLastMaximum_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) {i : Fin (m + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (m + 2)))
      (ULift.up (Fin.last (m + 1)))) :
    pathLastMaximum (pathLastReindex α P) = α.toOrderHom (pathLastMaximum P) := by
  apply le_antisymm
  · have hm := pathLastMaximum_mem (pathLastReindex α P)
    rcases hm with ⟨⟨k⟩, hk, he⟩
    induction k using Fin.lastCases with
    | last =>
      have he' := congrArg (fun k : ULift.{u} (Fin (n + 2)) ↦ k.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom (Fin.last (m + 1))).val =
        (pathLastMaximum (pathLastReindex α P)).val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last] at he'
      have hlt : (pathLastMaximum (pathLastReindex α P)).val < n + 1 :=
        (pathLastMaximum (pathLastReindex α P)).isLt
      change n + 1 = (pathLastMaximum (pathLastReindex α P)).val at he'
      omega
    | cast k =>
      have he' := congrArg (fun k : ULift.{u} (Fin (n + 2)) ↦ k.down.val) he
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom k.castSucc).val =
        (pathLastMaximum (pathLastReindex α P)).val at he'
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc] at he'
      have hmax : α.toOrderHom k = pathLastMaximum (pathLastReindex α P) := Fin.ext he'
      rw [← hmax]
      exact α.toOrderHom.monotone (le_pathLastMaximum P k hk)
  · apply le_pathLastMaximum (pathLastReindex α P)
    refine ⟨ULift.up (pathLastMaximum P).castSucc, pathLastMaximum_mem P, ?_⟩
    exact ULift.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc _ _)

/-- 概要：最大元による標準単体への射は各頂点で最大の前終点を返す。
方針：nerve の後合成と標準単体の nerve 表示の逆を評価する。
規約：入力の単体の次数は任意。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、比較の Hom の作用の成分計算。 -/
lemma pathLastMaximumMap_apply {n : ℕ} (i : Fin (n + 1))
    {d : SimplexCategoryᵒᵖ}
    (F : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) (k : Fin (d.unop.len + 1)) :
    ((pathLastMaximumMap i).app d F).down.toOrderHom k = pathLastMaximum (F.obj k) := by
  rcases d with ⟨⟨d⟩⟩
  change ((stdSimplex.isoNerve n).inv.app _
    ((nerveMap (pathLastMaximumFunctor i)).app _ F)) k = _
  rw [stdSimplex.isoNerve_inv_app_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
