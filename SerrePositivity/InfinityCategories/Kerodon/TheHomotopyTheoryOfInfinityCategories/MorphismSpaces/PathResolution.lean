module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PinchedFlagMap

/-!
概要：任意の path の単体を最初の最大元で正規化して旗の解像へ写す。
方針：最後の頂点を除き、最初の段の最大元以上に切り詰める。
規約：始点が動く正規化は旗の引き戻しの規約と一致する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像からの写像を coherent な単体へ戻す構成。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：path の包含は最後の頂点以外の有限集合の包含を与える。
方針：有限集合の所属条件を path の集合の所属に戻す。
規約：両 path の端点は同じ。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、path の単体の正規化の単調性。 -/
lemma pathBeforeLast_mono {n : ℕ} {i : Fin (n + 1)}
    {P Q : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))} (h : P.I ⊆ Q.I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast P ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast Q := by
  classical
  intro j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h (Finset.mem_filter.mp hj).2⟩

/-- 概要：path の単体を最初の最大元で切り詰めて正規化した旗にする。
方針：各段から終点を除き、最初の段の最大元以上の部分を取る。
規約：元の始点でなく、最初の段の最大元が新しい始点。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣 Hom の単体から旗への写像。 -/
noncomputable def pathFlagResolution {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d where
  start := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj 0)
  sets k := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (P.obj k)).filter (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj 0) ≤ j)
  monotone_sets := by
    intro k l h j hj
    obtain ⟨hj, ht⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr
      ⟨pathBeforeLast_mono (P.map (homOfLE h)).1.1.1 hj, ht⟩
  first := by
    ext j
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, ht⟩
      exact le_antisymm (Finset.le_max' _ _ hj) ht
    · rintro rfl
      exact ⟨Finset.max'_mem _ _, le_rfl⟩
  lower k j hj := (Finset.mem_filter.mp hj).2

/-- 概要：path の単体を正規化しても各段の最大元は変わらない。
方針：最大元は切断点以上なので残り、切り詰めは新しい点を追加しない。
規約：最初の段の最大元で切断する。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、正規化と射影の可換性。 -/
lemma pathFlagResolution_maxAt {n d : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (k : Fin (d + 1)) :
    (pathFlagResolution P).maxAt k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj k) := by
  apply le_antisymm
  · apply Finset.le_max'
    exact (Finset.mem_filter.mp ((pathFlagResolution P).maxAt_mem k)).1
  · apply (pathFlagResolution P).le_maxAt
    apply Finset.mem_filter.mpr
    exact ⟨Finset.max'_mem _ _,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mono (P.map (homOfLE (Fin.zero_le k))).1.1.1⟩

/-- 概要：path の単体の正規化は添字の引き戻しと整合する。
方針：引き戻した最初の最大元は元の切断点以上なので二重の切断をまとめる。
規約：元の path の始点 i は固定する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、path の Hom から解像への射の自然性。 -/
lemma pathFlagResolution_pullback {n d e : ℕ} {i : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) (α : Fin (e + 1) →o Fin (d + 1)) :
    (pathFlagResolution P).pullback α = pathFlagResolution (α.toFunctor ⋙ P) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact pathFlagResolution_maxAt P (α 0)
  · funext k
    apply Finset.ext
    intro j
    change j ∈ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (P.obj (α k))).filter
      (fun l ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj 0) ≤ l)).filter
        (fun l ↦ (pathFlagResolution P).maxAt (α 0) ≤ l) ↔
      j ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (P.obj (α k))).filter
        (fun l ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (P.obj (α 0)) ≤ l)
    rw [pathFlagResolution_maxAt]
    simp only [Finset.mem_filter]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mono (P.map (homOfLE (Fin.zero_le (α 0)))).1.1.1
    exact ⟨fun ⟨⟨hj, _⟩, ht⟩ ↦ ⟨hj, ht⟩,
      fun ⟨hj, ht⟩ ↦ ⟨⟨hj, h.trans ht⟩, ht⟩⟩

/-- 概要：path の豊穣 Hom から標準単体の旗の解像への正規化射。
方針：各次数で path の単体を正規化し、引き戻しの整合性を使う。
規約：元の始点 i は任意。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗からの写像を coherent 単体へ戻す際の Hom の作用。 -/
noncomputable def pathResolutionMap {n : ℕ} (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex n where
  app d := ↾fun P ↦ ULift.up (pathFlagResolution P)
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro P
    apply ULift.ext
    exact (pathFlagResolution_pullback P α.unop.toOrderHom).symm

/-- 概要：旗から作った path の前終点集合は元の旗の集合。
方針：castSucc の頂点の所属の特徴づけを使う。
規約：追加した最後の頂点を除いた集合で比較する。
使われ方：Kerodon Example 4.6.7.27（Tag 01M0）、旗を path の単体へ写す操作の回収。 -/
lemma CoherentResolutionFlag.pathBeforeLast_toPath {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) (k : Fin (d + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (F.toPath.{u} k) = F.sets k := by
  classical
  ext j
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast, Finset.mem_filter, Finset.mem_univ, true_and]
    using F.mem_toPath k j

/-- 概要：旗を path の単体にして正規化すると元の旗を回収する。
方針：前終点集合を回収し、最初の最大元は元の始点なので切断が何も変えないことを使う。
規約：正規化した旗の全次数で成立する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、二つの変換の逆性の旗側の計算。 -/
lemma CoherentResolutionFlag.pathFlagResolution_pathFlag {n d : ℕ}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) : pathFlagResolution F.pathFlag.{u} = F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (F.toPath 0) = F.start
    exact (F.pathLastMaximum_toPath 0).trans F.maxAt_zero
  · funext k
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast (F.toPath k)).filter
      (fun j ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (F.toPath 0) ≤ j) = F.sets k
    rw [F.pathBeforeLast_toPath, F.pathLastMaximum_toPath, F.maxAt_zero]
    apply Finset.filter_eq_self.mpr
    intro j hj
    exact F.lower k j hj

/-- 概要：path の正規化から解像の射影を取ると最大の前終点の射。
方針：各段の正規化後の最大元を計算する。
規約：追加した終点を除く最大元を使う。
使われ方：Kerodon Construction 4.6.7.22（Tag 01LV）、比較射を解像の射影から構成するための可換式。 -/
lemma pathResolutionMap_projection {n : ℕ} (i : Fin (n + 1)) :
    pathResolutionMap.{u} i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjection n = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  exact pathFlagResolution_maxAt P k

/-- 概要：前半の path の合成は後半の正規化した旗を変えない。
方針：前半の点は切断点以下で、正規化後に残れば共通の接合点に等しいことを使う。
規約：前半の終点は追加した最後の頂点より前の頂点 j。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、逆方向の構成の豊穣合成則。 -/
lemma pathFlagResolution_comp {n d : ℕ} {i j : Fin (n + 1)}
    (P : Fin (d + 1) ⥤ Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))
    (Q : Fin (d + 1) ⥤ Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    pathFlagResolution (P.prod' Q ⋙ compFunctor
      (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩) = pathFlagResolution Q := by
  classical
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag.ext
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_comp (P.obj 0) (Q.obj 0)
  · funext k
    apply Finset.ext
    intro l
    simp only [pathFlagResolution, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change ((ULift.up l.castSucc ∈ (P.obj k).I ∪ (Q.obj k).I) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (@CategoryStruct.comp
        (SimplicialThickening (ULift.{u} (Fin (n + 2)))) _
        ⟨ULift.up i.castSucc⟩ ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩
        (P.obj 0) (Q.obj 0)) ≤ l) ↔
      (ULift.up l.castSucc ∈ (Q.obj k).I ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (Q.obj 0) ≤ l)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_comp]
    constructor
    · rintro ⟨hl | hl, ht⟩
      · have hlj : l ≤ j := Fin.castSucc_le_castSucc_iff.mp ((P.obj k).le_right _ hl)
        have hjl : j ≤ l := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum (Q.obj 0) j (Q.obj 0).left).trans ht
        have heq : l = j := le_antisymm hlj hjl
        subst l
        exact ⟨(Q.obj k).left, ht⟩
      · exact ⟨hl, ht⟩
    · rintro ⟨hl, ht⟩
      exact ⟨Or.inr hl, ht⟩

/-- 概要：正規化射は始域側の path の合成を無視する。
方針：単体ごとの正規化した旗の合成則を使う。
規約：豊穣合成の各単体での計算。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、逆方向の豊穣関手の合成則。 -/
lemma pathResolutionMap_comp {n : ℕ} (i j : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (P : (nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc))).obj d)
    (Q : (nerve (Path (ULift.up j.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1))))).obj d) :
    (pathResolutionMap i).app d
      ((eComp SSet (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
        ⟨ULift.up j.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩).app d (P, Q)) =
          (pathResolutionMap j).app d Q := by
  apply ULift.ext
  exact pathFlagResolution_comp P Q

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
