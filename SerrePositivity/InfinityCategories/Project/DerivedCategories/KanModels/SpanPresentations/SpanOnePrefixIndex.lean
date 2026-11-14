module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.SpanIndexGeometry
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Signs

/-! # 固定一点を加えた未知集合の切断と符号

概要：後続集合に先頭の一点を加えると、余錐頂点での切断は二点集合と後続集合になる。
方針：後続集合を終区間として扱い、有限集合の外延性と削除の濃度を使う。
規約：HA Proposition 1.3.1.10。使われ方：D7 の脚側の残差の符号計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories


/-- 概要：余錐頂点より前の点は後続集合に属さない。
方針：後続集合の下界で判定する。
規約：固定二頂点のいずれにも適用可能。使われ方：一点追加の濃度。 -/
lemma spanPrefix_notMem_suffix {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    a ∉ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le]
  exact not_le_of_gt ha

/-- 概要：固定一点追加後の濃度は n+3。
方針：新しい点の不所属と後続集合の濃度を使う。
規約：全次元。使われ方：脚側の未知成分の次数。 -/
lemma card_spanSuffix_insert {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).card = n + 3 := by
  rw [Finset.card_insert_of_notMem (spanPrefix_notMem_suffix a ha), _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces]

/-- 概要：固定一点追加後の最小元は追加した点。
方針：後続集合の全点が追加点より後にあることを使う。
規約：追加点は余錐頂点より前。使われ方：脚側の未知成分の始点。 -/
lemma spanSuffix_insert_min {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)
    (h : (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).Nonempty) :
    a = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).min' h := by
  apply IsLeast.unique _ ((insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).isLeast_min' h)
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact le_rfl
  · exact ha.le.trans ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le i).mp hi)

/-- 概要：固定一点追加後の最大元は最後の頂点。
方針：最後の可変頂点の所属と有限添字の上界を使う。
規約：追加点の位置には依存しない。使われ方：脚側の未知成分の終点。 -/
lemma spanSuffix_insert_max {n : ℕ} (a : Fin (n + 4))
    (h : (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).Nonempty) :
    Fin.last (n + 3) = (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).max' h :=
  (show IsGreatest ((insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n) : Finset _) : Set (Fin (n + 4)))
      (Fin.last (n + 3)) from
    ⟨Finset.mem_insert_of_mem ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces _).mpr (by change 2 ≤ n + 3; omega)),
      fun i _ => Fin.le_last i⟩).unique ((insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).isGreatest_max' h)

/-- 概要：余錐頂点以下の左切断は追加点と余錐頂点の二点集合。
方針：後続点が余錐頂点以下ならその点自身に等しい。
規約：追加点は余錐頂点より前。使われ方：Bianchi に残る脚の同定。 -/
lemma spanSuffix_insert_leftCut {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).filter (· ≤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = {a, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n} := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le]
  constructor
  · rintro ⟨rfl | hi, hle⟩
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm hle hi)
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, ha.le⟩
    · exact ⟨Or.inr le_rfl, le_rfl⟩

/-- 概要：余錐頂点以上の右切断は元の後続集合。
方針：追加した点が余錐頂点より前にあることを使う。
規約：固定二頂点に適用可能。使われ方：Bianchi に残る共通残差。 -/
lemma spanSuffix_insert_rightCut {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n ≤ ·) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le]
  constructor
  · rintro ⟨rfl | hi, hge⟩
    · exact False.elim (not_le_of_gt ha hge)
    · exact hi
  · intro hi
    exact ⟨Or.inr hi, hi⟩

/-- 概要：余錐頂点より後の集合は後続集合からその頂点を除いた集合。
方針：終区間の下界と狭義不等式を比較する。
規約：追加点は余錐頂点より前。使われ方：残差寄与の符号の指数。 -/
lemma spanSuffix_insert_above {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)).filter (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n < ·) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le]
  constructor
  · rintro ⟨rfl | hi, hgt⟩
    · exact False.elim ((not_lt_of_ge ha.le) hgt)
    · exact ⟨ne_of_gt hgt, hi⟩
  · rintro ⟨hne, hge⟩
    exact ⟨Or.inr hge, lt_of_le_of_ne hge hne.symm⟩

/-- 概要：余錐頂点の残差寄与の符号は (-1)^(n+1)。
方針：余錐頂点より後の n+1 点を数える。
規約：整数の単位群の符号。使われ方：脚側右辺の微分の係数。 -/
lemma spanSuffix_insert_sign {n : ℕ} (a : Fin (n + 4)) (ha : a < _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (insert a (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n) = ((n : ℤ) + 1).negOnePow := by
  have hc := Finset.card_erase_add_one
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mem_spanSuffixFaces_iff_le (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)).mpr le_rfl)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.card_spanSuffixFaces] at hc
  have he : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanSuffixFaces n).erase (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.spanApex n)).card = n + 1 := by omega
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, spanSuffix_insert_above a ha, he, Nat.cast_add, Nat.cast_one]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
