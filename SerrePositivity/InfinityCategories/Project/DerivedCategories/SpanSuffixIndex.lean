module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData

/-! # span の標準セルの既知面の添字

概要：先頭の二頂点を固定し、後続の全頂点を除く面を境界の既知面として指定する。
方針：二回の succ の像で面集合を表し、その値の条件から境界面番号を回収する。
規約：先頭二点は A,B または A,C。使われ方：D7 の coslice の二セルの成分回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories


/-- 概要：可変因子の境界に対応する面番号の集合。
方針：n+2 点の添字を二回 succ で移す。
規約：先頭の二点は含めない。使われ方：二セルの既知面の指定。 -/
def spanSuffixFaces (n : ℕ) : Finset (Fin (n + 4)) :=
  Finset.univ.image (fun j : Fin (n + 2) ↦ j.succ.succ)

/-- 概要：選んだ面の添字は二以上の値に限る。
方針：二回の succ の像と自然数の差で両向きを示す。
規約：上界は有限添字の型に含む。使われ方：境界面の回収。 -/
lemma mem_spanSuffixFaces {n : ℕ} (j : Fin (n + 4)) :
    j ∈ spanSuffixFaces n ↔ 2 ≤ j.val := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    change 2 ≤ i.val + 1 + 1
    omega
  · intro h
    refine Finset.mem_image.mpr ⟨⟨j.val - 2, by have := j.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (j.val - 2) + 1 + 1 = j.val
    omega

/-- 概要：選んだ大きい面から可変因子の境界面番号を回収する。
方針：添字の値から二を引く。
規約：所属条件が下界を保証する。使われ方：coslice 境界の面への参照。 -/
def spanSuffixFaceIndex {n : ℕ} (j : Fin (n + 4)) (hj : j ∈ spanSuffixFaces n) :
    Fin (n + 2) := ⟨j.val - 2, by have := j.isLt; have := (mem_spanSuffixFaces j).mp hj; omega⟩

/-- 概要：回収した境界面番号を二回 succ すると元の番号に戻る。
方針：二以上の値から二を引いて足し戻す。
規約：有限順序集合の厳密な等式。使われ方：二セルの面の式の適用。 -/
lemma spanSuffixFaceIndex_succ_succ {n : ℕ} (j : Fin (n + 4))
    (hj : j ∈ spanSuffixFaces n) : (spanSuffixFaceIndex j hj).succ.succ = j := by
  apply Fin.ext
  have := (mem_spanSuffixFaces j).mp hj
  change (j.val - 2) + 1 + 1 = j.val
  omega

/-- 概要：選んだ面の集合は全ての頂点を覆う。
方針：二番目と三番目の頂点を除く面の少なくとも一方が指定頂点を避ける。
規約：n=0 も含む。使われ方：既知面から対象族を回収する被覆条件。 -/
lemma spanSuffixFaces_covers (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (spanSuffixFaces n) := by
  intro k
  by_cases hk : k = (⟨2, by omega⟩ : Fin (n + 4))
  · refine ⟨⟨3, by omega⟩, (mem_spanSuffixFaces _).mpr (by change 2 ≤ 3; decide), ?_⟩
    rw [hk]
    intro h
    have hv := congrArg Fin.val h
    change 3 = 2 at hv
    omega
  · exact ⟨⟨2, by omega⟩, (mem_spanSuffixFaces _).mpr (by change 2 ≤ 2; decide), Ne.symm hk⟩

/-- 概要：既知成分とは可変頂点を少なくとも一つ欠く成分。
方針：選んだ面集合の包含の否定を存在条件に書き換える。
規約：固定の先頭二頂点の所属は自由。使われ方：未知成分だけを別に与える条件。 -/
lemma spanSuffixFaces_known_iff {n : ℕ} (I : Finset (Fin (n + 4))) :
    (∃ j ∈ spanSuffixFaces n, j ∉ I) ↔ ¬ spanSuffixFaces n ⊆ I := by
  simp only [Finset.subset_iff, not_forall, exists_prop]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
