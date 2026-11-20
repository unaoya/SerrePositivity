module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexHABeadWord

/-! # 元の部分集合 bead の未処理の右側頂点
概要：右側の非空な頂点集合に、それより左の一点を加えた元の bead を作る。
方針：同じ元の最小・最大頂点と濃度を計算し、端点付きの連結語へ移す。
規約：頂点を別の順序に置換しない。使われ方：全 tensor 生成元の連結語への読み替え。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の右側頂点集合より厳密に左の点は、同じ集合に属さない。 -/
lemma simplexHABeadTail_not_mem {n : ℕ} (T : Finset (Fin (n + 1)))
    (a : Fin (n + 1)) (ha : ∀ t ∈ T, a < t) : a ∉ T := by
  intro h
  exact (ha a h).false

/-- 元の右側頂点集合に左端点を加えても、元の最大頂点は変わらない。 -/
lemma simplexHABeadTail_max {n : ℕ} (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (a : Fin (n + 1)) (ha : ∀ t ∈ T, a < t) :
    (insert a T).max' (Finset.insert_nonempty a T) = T.max' hT := by
  apply (Finset.max'_eq_iff _ _ _).mpr
  constructor
  · exact Finset.mem_insert_of_mem (Finset.max'_mem T hT)
  · intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact (ha _ (Finset.max'_mem T hT)).le
    · exact Finset.le_max' T b hb

/-- 元の端点を等号で指定した、元の同じ部分集合 bead の語。 -/
def simplexHABeadWordAt {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (a b : Fin (n + 1)) (ha : a = I.min' (Finset.card_pos.mp (by omega)))
    (hb : b = I.max' (Finset.card_pos.mp (by omega))) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b (I.card - 2) := by
  subst a b
  exact .bead I hI

/-- 元の非空な右側頂点集合に、元の左端点を加えた同じ部分集合 bead の語。 -/
def simplexHABeadTail {n : ℕ} (T : Finset (Fin (n + 1))) (hT : T.Nonempty)
    (a : Fin (n + 1)) (ha : ∀ t ∈ T, a < t) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a (T.max' hT) (T.card - 1) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha
  have hc : (insert a T).card = T.card + 1 := Finset.card_insert_of_notMem hn
  have hp : 0 < T.card := Finset.card_pos.mpr hT
  have hI : 2 ≤ (insert a T).card := by omega
  have hmin : a = (insert a T).min' (Finset.card_pos.mp (by omega)) := by
    symm
    apply (Finset.min'_eq_iff _ _ _).mpr
    constructor
    · exact Finset.mem_insert_self a T
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact le_rfl
      · exact (ha b hb).le
  have hd : (insert a T).card - 2 = T.card - 1 := by omega
  rw [← hd]
  exact _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordAt (insert a T) hI a (T.max' hT) hmin
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_max T hT a ha).symm

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
