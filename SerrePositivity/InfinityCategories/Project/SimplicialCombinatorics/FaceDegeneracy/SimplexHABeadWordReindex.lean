module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexHABeadWord

/-! # 元の bead 連結語の右端点と自由次元の移送
概要：同じ語を、右端点と自由次元の等号だけで再添字付けする。
方針：二つの等号を消去し、元の同じ語を返す。
規約：頂点集合と連結順を変更しない。使われ方：全生成元の読み替えの再帰式。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の語を、右端点と自由次元の等号だけで同じ語へ移送する。 -/
def simplexHABeadWordReindex {n : ℕ} {a b c : Fin (n + 1)} {p q : ℕ}
    (hb : b = c) (hd : p = q) (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a c q := by
  cases hb
  cases hd
  exact word

/-- 元の右端点・自由次元の移送前後で、語そのものは異種等号で一致する。 -/
lemma simplexHABeadWordReindex_heq {n : ℕ} {a b c : Fin (n + 1)} {p q : ℕ}
    (hb : b = c) (hd : p = q) (word : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexHABeadWord n a b p) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexHABeadWordReindex hb hd word) word := by
  cases hb
  cases hd
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
