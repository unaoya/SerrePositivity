module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionExtension

/-!
概要：有限集合の旗を coherent nerve の path の旗として表す。
方針：各集合に最後の頂点を追加し、引き戻しの切断点の前後で path を分解する。
規約：包含順序の右模型。単体的圏の豊穣 Hom の中で評価するための座標。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、Example 4.6.7.27（Tag 01M0）、補助解像と coherent Hom の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：旗の一段に最後の頂点を加えて path とする。
方針：始点から最後の頂点への区間内で、元の有限集合と終点の和集合を取る。
規約：元の頂点は castSucc で一段大きい順序集合へ入れる。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗を豊穣 Hom の単体として評価する座標。 -/
def CoherentResolutionFlag.toPath {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (d + 1)) :
    Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  I := {k | k.down = Fin.last (n + 1) ∨ ∃ j ∈ F.sets i, k.down = j.castSucc}
  left := Or.inr ⟨_, F.start_mem i, rfl⟩
  right := Or.inl rfl
  left_le k hk := by
    change F.start.castSucc ≤ k.down
    rcases hk with hk | ⟨j, hj, hk⟩
    · rw [hk]
      exact Fin.le_last _
    · rw [hk]
      exact Fin.castSucc_le_castSucc_iff.mpr (F.lower i j hj)
  le_right k _ := Fin.le_last k.down

/-- 概要：追加した終点以外の path の点は元の旗の集合の点。
方針：castSucc の単射性と追加した終点との不一致を使う。
規約：点は元の Fin(n+1) で指定する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗と path の座標の相互変換。 -/
lemma CoherentResolutionFlag.mem_toPath {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (i : Fin (d + 1)) (j : Fin (n + 1)) :
    ULift.up j.castSucc ∈ (F.toPath.{u} i).I ↔ j ∈ F.sets i := by
  constructor
  · rintro (h | ⟨k, hk, h⟩)
    · exact False.elim (Fin.castSucc_ne_last j h)
    · have hjk : j = k := Fin.castSucc_injective _ h
      exact hjk.symm ▸ hk
  · intro h
    exact Or.inr ⟨j, h, rfl⟩

/-- 概要：旗から作った path の前終点の最大元は旗の最大元。
方針：両側の最大元の所属と上界性を比較する。
規約：最後に追加した終点は最大元の計算から除く。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、coherent Hom の比較と射影の一致。 -/
lemma CoherentResolutionFlag.pathLastMaximum_toPath {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (i : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (F.toPath.{u} i) = F.maxAt i := by
  apply le_antisymm
  · exact F.le_maxAt i _ ((F.mem_toPath i _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem _))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum _ _ ((F.mem_toPath i _).mpr (F.maxAt_mem i))

/-- 概要：旗の各段の path を包含の関手にまとめる。
方針：旗の包含の単調性で path の包含を示す。
規約：添字は小さい順序圏 Fin(d+1)。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣 Hom を評価する nerve の単体。 -/
def CoherentResolutionFlag.pathFlag {n d : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    Fin (d + 1) ⥤ Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))) where
  obj i := F.toPath i
  map {i j} f := ⟨⟨⟨by
    intro k hk
    rcases hk with hk | ⟨l, hl, hk⟩
    · exact Or.inl hk
    · exact Or.inr ⟨l, F.monotone_sets f.le hl, hk⟩⟩⟩⟩

/-- 概要：引き戻しで選んだ最初の段の最大元までの前半の path。
方針：選んだ各段を切断点以下に制限する。
規約：最初の段の最大元は全ての選んだ段に属する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗の引き戻しの豊穣合成による説明。 -/
def CoherentResolutionFlag.prefixPath {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (i : Fin (e + 1)) :
    Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (F.maxAt (α 0)).castSucc) where
  I := {k | ∃ j ∈ F.sets (α i), j ≤ F.maxAt (α 0) ∧ k.down = j.castSucc}
  left := ⟨_, F.start_mem _, F.lower _ _ (F.maxAt_mem _), rfl⟩
  right := ⟨_, F.monotone_sets (α.monotone (Fin.zero_le i)) (F.maxAt_mem _), le_rfl, rfl⟩
  left_le k hk := by
    obtain ⟨j, hj, _, heq⟩ := hk
    change F.start.castSucc ≤ k.down
    rw [heq]
    exact Fin.castSucc_le_castSucc_iff.mpr (F.lower _ _ hj)
  le_right k hk := by
    obtain ⟨j, _, hj, heq⟩ := hk
    change k.down ≤ (F.maxAt (α 0)).castSucc
    rw [heq]
    exact Fin.castSucc_le_castSucc_iff.mpr hj

/-- 概要：切断点までの前半の path は選んだ段に関して単調。
方針：切断点を固定したまま元の旗の包含を使う。
規約：値域は追加した最後の頂点を含まない path。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、固定面が豊穣恒等になることの適用先。 -/
def CoherentResolutionFlag.prefixFlag {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    Fin (e + 1) ⥤ Path (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (F.maxAt (α 0)).castSucc) where
  obj i := F.prefixPath α i
  map {i j} f := ⟨⟨⟨by
    intro k hk
    obtain ⟨l, hl, ht, hk⟩ := hk
    exact ⟨l, F.monotone_sets (α.monotone f.le) hl, ht, hk⟩⟩⟩⟩

/-- 概要：選んだ path は切断点の前半と正規化した後半の合成。
方針：有限集合を切断点以下と切断点以上の二部分の和集合に分ける。
規約：後半は旗の引き戻しの定義そのもの。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の引き戻しの豊穣合成による計算。 -/
lemma CoherentResolutionFlag.prefixPath_comp_pullback {n d e : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1))
    (i : Fin (e + 1)) :
    @CategoryStruct.comp (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
      ⟨ULift.up F.start.castSucc⟩ ⟨ULift.up (F.maxAt (α 0)).castSucc⟩
      ⟨ULift.up (Fin.last (n + 1))⟩
      (F.prefixPath α i) ((F.pullback α).toPath i) = F.toPath (α i) := by
  apply SimplicialThickening.Path.ext
  apply Set.ext
  intro k
  change ((∃ j ∈ F.sets (α i), j ≤ F.maxAt (α 0) ∧ k.down = j.castSucc) ∨
      (k.down = Fin.last (n + 1) ∨
        ∃ j ∈ (F.sets (α i)).filter (fun l ↦ F.maxAt (α 0) ≤ l),
          k.down = j.castSucc)) ↔
      k.down = Fin.last (n + 1) ∨ ∃ j ∈ F.sets (α i), k.down = j.castSucc
  constructor
  · rintro (⟨j, hj, _, hk⟩ | hk | ⟨j, hj, hk⟩)
    · exact Or.inr ⟨j, hj, hk⟩
    · exact Or.inl hk
    · exact Or.inr ⟨j, (Finset.mem_filter.mp hj).1, hk⟩
  · rintro (hk | ⟨j, hj, hk⟩)
    · exact Or.inr (Or.inl hk)
    · by_cases h : j ≤ F.maxAt (α 0)
      · exact Or.inl ⟨j, hj, h, hk⟩
      · exact Or.inr (Or.inr ⟨j, Finset.mem_filter.mpr
          ⟨hj, le_of_not_ge h⟩, hk⟩)

/-- 概要：旗の単体の選択は前半と引き戻した後半の豊穣合成。
方針：対象ごとの path の分解を、path の圏の射の一意性で関手の等式にする。
規約：前半・後半は同じ添字を持つ関手として同時に合成する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、coherent 単体の評価の自然性。 -/
lemma CoherentResolutionFlag.prefixFlag_comp_pullback {n d e : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (α : Fin (e + 1) →o Fin (d + 1)) :
    (F.prefixFlag.{u} α).prod' ((F.pullback α).pathFlag) ⋙
      compFunctor (⟨ULift.up F.start.castSucc⟩ :
        SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up (F.maxAt (α 0)).castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ =
      α.toFunctor ⋙ F.pathFlag := by
  apply CategoryTheory.Functor.ext (fun i ↦ F.prefixPath_comp_pullback α i)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
