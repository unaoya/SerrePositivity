module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentHomPost
public import Mathlib.Data.Finset.Max

/-!
概要：初点からの path の最初の正頂点を選ぶ座標と豊穣合成の整合性。
方針：零頂点を除いた有限集合の最小元を取り、包含と後半の合成を計算する。
規約：Mathlib の path の包含に対して最小元は反単調となる。
使われ方：Kerodon §4.6.7（Tag 01LA）、HTT 4.2.4.1 の重み付き nerve と左 coslice の比較。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SimplicialThickening
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：初点零からの path の正頂点の有限集合。
方針：succ により零以外の点を列挙して path への所属で絞る。
規約：値は零頂点を除いた Fin(n+1) の添字。
使われ方：HTT 4.2.4.1 の左 coslice の Hom の座標。 -/
noncomputable def pathAfterFirst {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun k ↦ ULift.up k.succ ∈ P.I)

/-- 概要：正頂点の有限集合は終点を含み空でない。
方針：path の終点の所属を用いる。
規約：終点は j.succ で正である。
使われ方：HTT 4.2.4.1 の最小点の存在。 -/
lemma pathAfterFirst_nonempty {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    (pathAfterFirst P).Nonempty := by
  classical
  exact ⟨j, by simp [pathAfterFirst, P.right]⟩

/-- 概要：path の最初の正頂点の添字。
方針：正頂点の有限集合の最小元を取る。
規約：零を除いた添字なので元の頂点は値の succ。
使われ方：HTT 4.2.4.1 の重みの初区間への評価。 -/
noncomputable def pathFirstMinimum {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) : Fin (n + 1) :=
  (pathAfterFirst P).min' (pathAfterFirst_nonempty P)

/-- 概要：選んだ最初の正頂点は path に属する。
方針：有限集合の最小元の所属を使う。
規約：元の頂点へは succ で戻す。
使われ方：HTT 4.2.4.1 の包含と合成の比較。 -/
lemma pathFirstMinimum_mem {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    ULift.up (pathFirstMinimum P).succ ∈ P.I := by
  classical
  exact (Finset.mem_filter.mp
    (Finset.min'_mem (pathAfterFirst P) (pathAfterFirst_nonempty P))).2

/-- 概要：最初の正頂点の添字は他の正頂点の添字以下。
方針：有限集合の最小元の下界性を使う。
規約：点 k は零を除いた添字。
使われ方：HTT 4.2.4.1 の係数評価の反単調性。 -/
lemma pathFirstMinimum_le {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ))
    (k : Fin (n + 1)) (hk : ULift.up k.succ ∈ P.I) : pathFirstMinimum P ≤ k := by
  classical
  apply Finset.min'_le
  simp only [pathAfterFirst, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hk

/-- 概要：path の包含は最初の正頂点を減少させる。
方針：小さい path の最小点の所属を大きい path に移す。
規約：path の射の方向と係数の頂点の順序は逆。
使われ方：HTT 4.2.4.1 の反転した係数への射の構成。 -/
lemma pathFirstMinimum_antitone {n : ℕ} {j : Fin (n + 1)}
    {P Q : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)}
    (h : P.I ⊆ Q.I) : pathFirstMinimum Q ≤ pathFirstMinimum P :=
  pathFirstMinimum_le Q _ (h (pathFirstMinimum_mem P))

/-- 概要：最初の正頂点は終点以下。
方針：終点の所属と最小元の下界性を使う。
規約：零を除いた添字でも同じ不等式。
使われ方：HTT 4.2.4.1 の初区間の重みへの因子化。 -/
lemma pathFirstMinimum_le_end {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathFirstMinimum P ≤ j :=
  pathFirstMinimum_le P j P.right

/-- 概要：正頂点から始まる後半を合成しても最初の正頂点は変わらない。
方針：後半の全点は切断点以上であり、前半の最小点は切断点以下。
規約：切断点は i.succ であり零ではない。
使われ方：HTT 4.2.4.1 の左 coslice の豊穣合成則。 -/
lemma pathFirstMinimum_comp {n : ℕ} {i j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up i.succ))
    (Q : Path (ULift.up i.succ : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    pathFirstMinimum
      (@CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
        ⟨ULift.up 0⟩ ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ P Q) =
      pathFirstMinimum P := by
  let R : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) :=
    @CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
      ⟨ULift.up 0⟩ ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ P Q
  change pathFirstMinimum R = pathFirstMinimum P
  apply le_antisymm
  · exact pathFirstMinimum_le R _ (Or.inl (pathFirstMinimum_mem P))
  · have hm := pathFirstMinimum_mem R
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact pathFirstMinimum_le P _ hm
    · have hle := Q.left_le _ hm
      change i.succ ≤ (pathFirstMinimum R).succ at hle
      exact (pathFirstMinimum_le_end P).trans (Fin.succ_le_succ_iff.mp hle)

/-- 概要：最初の正頂点の添字を終点までの初区間に置く。
方針：終点以下という式で Fin(j+1) の境界条件を満たす。
規約：元の Fin(n+1) の値は変えない。
使われ方：HTT 4.2.4.1 の重み Δ[j] の評価の添字。 -/
noncomputable def pathFirstMinimumIndex {n : ℕ} {j : Fin (n + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) :
    Fin (j.val + 1) :=
  ⟨(pathFirstMinimum P).val, Nat.lt_succ_of_le (pathFirstMinimum_le_end P)⟩

/-- 概要：初区間内の最小点を反転すると path に単調な関手になる。
方針：最小点の反単調性と Fin.rev の順序反転を合成する。
規約：値域は Hom と同じ宇宙へ ULift する。
使われ方：HTT 4.2.4.1 の反転した初区間への nerve の射。 -/
noncomputable def pathFirstMinimumReverseFunctor {n : ℕ} (j : Fin (n + 1)) :
    Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ) ⥤
      ULift.{u} (Fin (j.val + 1)) where
  obj P := ULift.up (pathFirstMinimumIndex P).rev
  map f := homOfLE (by
    change (pathFirstMinimumIndex _).rev ≤ (pathFirstMinimumIndex _).rev
    apply Fin.rev_le_rev.mpr
    exact pathFirstMinimum_antitone f.1.1.1)

/-- 概要：初点からの path を反転した終点までの標準単体へ写す。
方針：反転最小点関手の nerve を標準単体へ移し、標準単体の反転同型で移す。
規約：値域は Δ[j] の反転。元の係数の反転を打ち消す入力となる。
使われ方：HTT 4.2.4.1 の重み付き nerve の係数から左 coslice への射。 -/
noncomputable def pathFirstMinimumMap {n : ℕ} (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      (Δ[j.val] : SSet.{u}).op :=
  nerveMap (pathFirstMinimumReverseFunctor j) ≫
    (stdSimplex.isoNerve j.val).inv ≫ (stdSimplex.opIso ⦋j.val⦌).inv


/-- 概要：初点固定拡張で path の全頂点を写す。
方針：部分集合の像を取り、単調性で終点の上界条件を移す。
規約：終点 j.succ は α(j).succ へ写る。
使われ方：HTT 4.2.4.1 の重みの添字変換。 -/
def pathFirstReindex {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) {j : Fin (m + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (m + 2))) (ULift.up j.succ)) :
    Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up (α j).succ) where
  I := (fun k : ULift.{u} (Fin (m + 2)) ↦ ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α k.down)) '' P.I
  left := ⟨ULift.up 0, P.left, rfl⟩
  right := ⟨ULift.up j.succ, P.right, rfl⟩
  left_le k _ := Fin.zero_le k.down
  le_right k hk := by
    rcases hk with ⟨l, hl, rfl⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α).monotone (P.le_right l hl)

/-- 概要：最初の正頂点の選択は初点を固定した任意の添字変換と可換。
方針：元の最小点の像と、像の最小点の原像で両方の不等式を示す。
規約：α は非単射でもよい。退化に追加の仮定を課さない。
使われ方：HTT 4.2.4.1 の比較の全ての面・退化との可換性。 -/
lemma pathFirstMinimum_reindex {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    {j : Fin (m + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (m + 2))) (ULift.up j.succ)) :
    pathFirstMinimum (pathFirstReindex α P) = α (pathFirstMinimum P) := by
  apply le_antisymm
  · apply pathFirstMinimum_le
    exact ⟨ULift.up (pathFirstMinimum P).succ, pathFirstMinimum_mem P, rfl⟩
  · have hm := pathFirstMinimum_mem (pathFirstReindex α P)
    rcases hm with ⟨⟨k⟩, hk, he⟩
    induction k using Fin.cases with
    | zero =>
      have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) ↦ a.down.val) he
      change 0 = (pathFirstMinimum (pathFirstReindex α P)).val + 1 at he'
      omega
    | succ k =>
      have he' := congrArg (fun a : ULift.{u} (Fin (n + 2)) ↦ a.down.val) he
      change (α k).val + 1 = (pathFirstMinimum (pathFirstReindex α P)).val + 1 at he'
      have hv : α k = pathFirstMinimum (pathFirstReindex α P) := Fin.ext (by omega)
      rw [← hv]
      exact α.monotone (pathFirstMinimum_le P k hk)


/-- 概要：初点固定の path の添字変換は包含圏の関手になる。
方針：部分集合の包含を像の包含へ写す。
規約：終点も α によって移す。
使われ方：HTT 4.2.4.1 の重み付き nerve の面・退化の比較。 -/
def pathFirstReindexFunctor {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (j : Fin (m + 1)) :
    Path (ULift.up 0 : ULift.{u} (Fin (m + 2))) (ULift.up j.succ) ⥤
      Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up (α j).succ) where
  obj := pathFirstReindex α
  map f := ⟨⟨⟨Set.image_mono f.1.1.1⟩⟩⟩

/-- 概要：反転した標準単体への座標射は各頂点で最初の正頂点を返す。
方針：nerve 表示の評価と標準単体の反転の式を計算する。
規約：反転した標準単体のパラメータの頂点 k は元の k.rev に対応する。
使われ方：HTT 4.2.4.1 の係数の評価と合成の成分計算。 -/
lemma pathFirstMinimumMap_apply {n : ℕ} (j : Fin (n + 1)) {d : SimplexCategoryᵒᵖ}
    (F : (nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2)))
      (ULift.up j.succ))).obj d) (k : Fin (d.unop.len + 1)) :
    (SSet.opObjEquiv ((pathFirstMinimumMap j).app d F)).down.toOrderHom k =
      pathFirstMinimumIndex (F.obj k.rev) := by
  rcases d with ⟨⟨d⟩⟩
  change (SSet.opObjEquiv (stdSimplex.opObjEquiv.{u, u}.symm
    ((stdSimplex.isoNerve j.val).inv.app _
      ((nerveMap (pathFirstMinimumReverseFunctor j)).app _ F)))) k = _
  rw [stdSimplex.opObjEquiv_opObjEquiv_symm_apply.{u, u}, stdSimplex.isoNerve_inv_app_apply]
  change (pathFirstMinimumIndex (F.obj k.rev)).rev.rev = _
  exact Fin.rev_rev _

/-- 概要：初区間内の最小点の添字は制限した単体写像と可換。
方針：自然数の値で比較し、最小点の添字変換の式を使う。
規約：元の simplex の α は面・退化を含む。
使われ方：HTT 4.2.4.1 の係数 Δ[j] の制限の自然性。 -/
lemma pathFirstMinimumIndex_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    {j : Fin (m + 1)}
    (P : Path (ULift.up 0 : ULift.{u} (Fin (m + 2))) (ULift.up j.succ)) :
    pathFirstMinimumIndex (pathFirstReindex α.toOrderHom P) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α j).toOrderHom (pathFirstMinimumIndex P) := by
  apply Fin.ext
  change (pathFirstMinimum (pathFirstReindex α.toOrderHom P)).val =
    (α.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixVertex j (pathFirstMinimumIndex P))).val
  rw [pathFirstMinimum_reindex]
  rfl


/-- 概要：最小点の標準単体への射は全ての初区間の添字変換と可換。
方針：各 simplex の頂点で座標を比較し、最小点の制限の式を使う。
規約：係数の反転と初点固定拡張を明示する。
使われ方：HTT 4.2.4.1 の重み付き nerve の面・退化の自然性。 -/
lemma pathFirstMinimumMap_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (j : Fin (m + 1)) :
    nerveMap (pathFirstReindexFunctor α.toOrderHom j) ≫
      pathFirstMinimumMap (α.toOrderHom j) =
    pathFirstMinimumMap j ≫
      SSet.opFunctor.map (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α j)) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro k
  change (SSet.opObjEquiv ((pathFirstMinimumMap (α.toOrderHom j)).app d
    (F ⋙ pathFirstReindexFunctor α.toOrderHom j))).down.toOrderHom k =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α j).toOrderHom
        ((SSet.opObjEquiv ((pathFirstMinimumMap j).app d F)).down.toOrderHom k)
  rw [pathFirstMinimumMap_apply, pathFirstMinimumMap_apply]
  exact pathFirstMinimumIndex_reindex α (F.obj k.rev)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
