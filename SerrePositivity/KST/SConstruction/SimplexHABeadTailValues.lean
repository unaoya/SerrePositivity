module
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordTransport

/-! # 未処理の右側頂点集合を持つ bead の実 HA 値
概要：右側頂点集合に左端点を加えた語の値は、同じ元の部分集合の HA 成分。
方針：元の端点付き一 bead の評価と、濃度による次元移送の計算を合成する。
規約：元の部分集合・端点・指定次数を保持。使われ方：全生成元読み替えの基底計算。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の右側頂点集合を持つ bead の語の評価は、同じ部分集合の HA 成分。 -/
lemma simplexHABeadTail_value {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (T : Finset (Fin (n + 1))) (hT : T.Nonempty) (a : Fin (n + 1))
    (ha : ∀ t ∈ T, a < t)
    (hI : 2 ≤ (insert a T).card)
    (hmin : a = (insert a T).min' (Finset.card_pos.mp (by omega)))
    (hmax : T.max' hT = (insert a T).max' (Finset.card_pos.mp (by omega))) :
    simplexHABeadWordValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail T hT a ha) =
      s.hom (insert a T) a (T.max' hT) (-((T.card - 1 : ℕ) : ℤ)) hI hmin hmax (by
        have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha)
        have _hp := Finset.card_pos.mpr hT
        omega) := by
  have hc := Finset.card_insert_of_notMem (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail_not_mem T a ha)
  have _hp := Finset.card_pos.mpr hT
  have hd : T.card - 1 = (insert a T).card - 2 := by omega
  unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadTail
  rw [simplexHABeadWordValue_mpr A s hd, simplexHABeadWordAt_value]
  exact simplexHAComponent_degree_transport A s _ _ _ _ _ _ _ _
    (by omega) (by omega) (by omega)

end SerrePositivity.KST.SConstruction
