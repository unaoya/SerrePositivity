module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PathMaximum

/-!
概要：二段の豊穣合成を記述する path の切替点以前の最大元。
方針：単調な二値ラベルが零である path の点を有限集合に集める。
規約：追加した最後の頂点は座標から除外する。
使われ方：パラメーター付きの coherent な合成 prism の豊穣 Hom の座標。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：path の点のうち切替前のラベルを持つ有限集合。
方針：元の n+1 頂点で所属と零ラベルを検査する。
規約：始点は切替前に置く。
使われ方：coherent な三対象の合成の最初の射の座標。 -/
noncomputable def pathCutBeforeLast {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} {j : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) :
    Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun k ↦ t k = 0 ∧ ULift.up k.castSucc ∈ P.I)

/-- 概要：切替前の始点を持つ path の座標集合は非空。
方針：始点の所属を使う。
規約：証明の選択は最大元の値に影響しない。
使われ方：最大座標の存在。 -/
lemma pathCutBeforeLast_nonempty {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) :
    (pathCutBeforeLast t P).Nonempty := by
  classical
  exact ⟨i, by simp [pathCutBeforeLast, hi, P.left]⟩

/-- 概要：切替前の点の最大座標。
方針：非空な有限集合の最大元を取る。
規約：戻り値は元の n 単体の頂点。
使われ方：豊穣な最初の射のパラメーター評価。 -/
noncomputable def pathCutMaximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) : Fin (n + 1) :=
  (pathCutBeforeLast t P).max' (pathCutBeforeLast_nonempty t hi P)

/-- 概要：最大座標は切替前であり path に属する。
方針：最大元の有限集合への所属を展開する。
規約：元の頂点へは castSucc で戻す。
使われ方：座標の単調性と合成則。 -/
lemma pathCutMaximum_spec {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)) :
    t (pathCutMaximum t hi P) = 0 ∧ ULift.up (pathCutMaximum t hi P).castSucc ∈ P.I := by
  classical
  have h := Finset.max'_mem (pathCutBeforeLast t P) (pathCutBeforeLast_nonempty t hi P)
  exact (Finset.mem_filter.mp h).2

/-- 概要：切替前の path の任意の点は最大座標以下。
方針：有限集合の最大元の上界性を使う。
規約：頂点の所属とラベルを明示する。
使われ方：path の包含と合成での座標比較。 -/
lemma le_pathCutMaximum {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j))
    (k : Fin (n + 1)) (hk : t k = 0) (hP : ULift.up k.castSucc ∈ P.I) :
    k ≤ pathCutMaximum t hi P := by
  classical
  apply Finset.le_max'
  simp only [pathCutBeforeLast, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hk, hP⟩

/-- 概要：path の包含は切替前の最大座標を増加させる。
方針：小さい path の最大元を大きい path の上界性に入れる。
規約：二つの端点とラベルは固定。
使われ方：豊穣 Hom 上の座標を nerve の射にする。 -/
lemma pathCutMaximum_mono {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i : Fin (n + 1)} (hi : t i = 0) {j : Fin (n + 2)}
    {P Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j)}
    (h : P.I ⊆ Q.I) : pathCutMaximum t hi P ≤ pathCutMaximum t hi Q :=
  le_pathCutMaximum t hi Q _ (pathCutMaximum_spec t hi P).1
    (h (pathCutMaximum_spec t hi P).2)

/-- 概要：切断点も切替前なら、合成した path の最大座標は後半の最大座標。
方針：前半の全点を切断点で抑え、後半の最大元と比較する。
規約：終点は追加した最後の頂点でもよい。
使われ方：三対象の coherent な合成の X→X→Y・X→X→Z の場合。 -/
lemma pathCutMaximum_comp_zero {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 0) {k : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (Q : Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up k)) :
    pathCutMaximum t hi ((compFunctor ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)) =
      pathCutMaximum t hj Q := by
  let R := (compFunctor ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)
  change pathCutMaximum t hi R = _
  apply le_antisymm
  · have hm := (pathCutMaximum_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · have hle := P.le_right _ hm
      change (pathCutMaximum t hi R).castSucc ≤ j.castSucc at hle
      exact (Fin.castSucc_le_castSucc_iff.mp hle).trans (le_pathCutMaximum t hj Q j hj Q.left)
    · exact le_pathCutMaximum t hj Q _ (pathCutMaximum_spec t hi R).1 hm
  · exact le_pathCutMaximum t hi R _ (pathCutMaximum_spec t hj Q).1
      (Or.inr (pathCutMaximum_spec t hj Q).2)

/-- 概要：切断点が切替後なら、合成した path の切替前の最大座標は前半のもの。
方針：後半に零ラベルの点が無いことを単調性で示す。
規約：追加した最後の頂点は座標集合に含まれない。
使われ方：三対象の coherent な合成の X→Y→Y・X→Y→Z の場合。 -/
lemma pathCutMaximum_comp_one {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i = 0) (hj : t j = 1) {k : Fin (n + 2)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc))
    (Q : Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up k)) :
    pathCutMaximum t hi ((compFunctor ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩
      (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)) =
      pathCutMaximum t hi P := by
  let R := (compFunctor ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩
    (⟨ULift.up k⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))).obj (P, Q)
  change pathCutMaximum t hi R = _
  apply le_antisymm
  · have hm := (pathCutMaximum_spec t hi R).2
    change _ ∈ P.I ∪ Q.I at hm
    rcases hm with hm | hm
    · exact le_pathCutMaximum t hi P _ (pathCutMaximum_spec t hi R).1 hm
    · have hle := Q.left_le _ hm
      change j.castSucc ≤ (pathCutMaximum t hi R).castSucc at hle
      have h := t.monotone (Fin.castSucc_le_castSucc_iff.mp hle)
      rw [hj, (pathCutMaximum_spec t hi R).1] at h
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) h)
  · exact le_pathCutMaximum t hi R _ (pathCutMaximum_spec t hi P).1
      (Or.inl (pathCutMaximum_spec t hi P).2)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
