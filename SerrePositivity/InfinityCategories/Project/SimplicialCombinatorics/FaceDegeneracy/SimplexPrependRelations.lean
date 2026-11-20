module


public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexPrepend

/-!
# 先頭への頂点追加と面・退化の関係

概要：先頭追加は標準の面と退化の番号を一つずらす。
方針：有限順序集合の零点と後続点で写像を比較する。
規約：Segal 1974 Proposition 1.6 の標準単体の余分な退化の恒等式の補助。
使われ方：標準形上の先頭追加の面・退化との整合。
-/

@[expose] public section
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory
open scoped _root_.Simplicial

/--
概要：最初の面を除いてから先頭追加した射を使うと、元の射と最初の面の合成になる。
方針：既存の後続点の計算を使う。
規約：任意の単体圏の射に適用できる。
使われ方：余分な退化の最初の面の恒等式。
-/
theorem simplexPrepend_δ_zero {m n : SimplexCategory} (θ : m ⟶ n) :
    SimplexCategory.δ (0 : Fin (m.len + 2)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ =
      θ ≫ SimplexCategory.δ (0 : Fin (n.len + 2)) := by
  ext i : 3
  rfl

/--
概要：面の先頭追加は番号を一つずらした面である。
方針：零点と後続点で標準の頂点を飛ばす写像を計算する。
規約：元の面の番号は i、新しい面の番号は i.succ。
使われ方：余分な退化と通常の面の交換。
-/
@[simp] theorem simplexPrepend_δ {n : ℕ} (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (SimplexCategory.δ i) = SimplexCategory.δ i.succ := by
  ext j : 3
  cases j using Fin.cases with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend, SimplexCategory.δ]
  | succ j => simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend, SimplexCategory.δ]

/--
概要：退化の先頭追加は番号を一つずらした退化である。
方針：零点と後続点で標準の頂点を重ねる写像を計算する。
規約：元の退化の番号は i、新しい退化の番号は i.succ。
使われ方：余分な退化と通常の退化の交換。
-/
@[simp] theorem simplexPrepend_σ {n : ℕ} (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend (SimplexCategory.σ i) = SimplexCategory.σ i.succ := by
  ext j : 3
  cases j using Fin.cases with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend, SimplexCategory.σ]
  | succ j => simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend, SimplexCategory.σ]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
