module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWordReindex
public import SerrePositivity.KST.SConstruction.SimplexHABeadWordCells

/-! # 元の bead 語の再添字付けと HA 評価・実鎖射
概要：右端点と自由次元の等号による語の移送は、同じ値と実鎖射の異種等号を保つ。
方針：元の端点等号と次元等号を消去して元の語の評価へ戻す。
規約：移送前後の具体的な値を保持。使われ方：読み替えの切断・辺の再帰の比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の右端点・自由次元の移送前後で、元の HA 語の値は異種等号で一致する。 -/
lemma simplexHABeadWordValue_reindex {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    {a b c : Fin (n + 1)} {p q : ℕ} (hb : b = c) (hd : p = q)
    (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p) :
    HEq (simplexHABeadWordValue A s (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex hb hd word))
      (simplexHABeadWordValue A s word) := by
  cases hb
  cases hd
  rfl

/-- 元の右端点・自由次元の移送前後で、元の語の実鎖射は異種等号で一致する。 -/
lemma simplexHABeadWordCell_reindex {n : ℕ} {a b c : Fin (n + 1)} {p q : ℕ}
    (hb : b = c) (hd : p = q) (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p) :
    HEq (simplexHABeadWordCell A (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex hb hd word))
      (simplexHABeadWordCell A word) := by
  cases hb
  cases hd
  rfl

end SerrePositivity.KST.SConstruction
