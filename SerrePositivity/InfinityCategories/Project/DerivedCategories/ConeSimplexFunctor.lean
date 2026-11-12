module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-! # 頂点を前置する単体圏の関手

概要：全順序写像の前に新しい零頂点を付ける操作を関手に束ねる。
方針：零と後続元で恒等・合成を計算し、面・退化生成元を同定する。
規約：頂点は常に始点へ追加する。使われ方：切断錐の全順序写像への自然性。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 各単体とその射に新しい始頂点を付ける関手。 -/
def coneSimplexFunctor : SimplexCategory ⥤ SimplexCategory where
  obj a := ⦋a.len + 1⦌
  map α := SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom α.toOrderHom)
  map_id a := by
    ext i : 3
    cases i using Fin.cases <;> rfl
  map_comp α β := by
    ext i : 3
    cases i using Fin.cases <;> rfl

/-- 前置は基本面の番号を一つ上げる。 -/
lemma coneSimplexFunctor_map_δ {n : ℕ} (i : Fin (n + 2)) :
    coneSimplexFunctor.map (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  change SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom _) = _
  ext j : 3
  cases j using Fin.cases with
  | zero =>
    change (0 : Fin (n + 3)) = i.succ.succAbove 0
    simp
  | succ j =>
    change (i.succAbove j).succ = i.succ.succAbove j.succ
    simp

/-- 前置は基本退化の番号を一つ上げる。 -/
lemma coneSimplexFunctor_map_σ {n : ℕ} (i : Fin (n + 1)) :
    coneSimplexFunctor.map (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  change SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom _) = _
  ext j : 3
  cases j using Fin.cases with
  | zero =>
    change (0 : Fin (n + 2)) = i.succ.predAbove 0
    simp
  | succ j =>
    change (i.predAbove j).succ = i.succ.predAbove j.succ
    simp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
