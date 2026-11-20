module


public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexPrependRelations

/-!
# 標準単体の頂点写像の先頭への零点の追加

概要：標準単体の頂点写像に零点を追加し、単射との合成との整合を計算する。
方針：零点と後続点を場合分けした単調写像を使う。
規約：Segal 1974 Proposition 1.6 の標準単体の自由な退化の収縮の補助。
使われ方：標準形の行の単体への余分な退化。
-/

@[expose] public section
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory
open scoped _root_.Simplicial

/--
概要：標準単体の頂点写像の先頭に零点を追加する。
方針：新しい最初の頂点を零点へ、他の頂点を元の写像の値へ送る。
規約：始域の次元だけが一つ増える。
使われ方：自由な退化の標準形の行の単体の拡張。
-/
def simplexConeZero {k : SimplexCategory} {n : ℕ} (x : k ⟶ ⦋n⦌) : ⦋k.len + 1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    { toFun := Fin.cases 0 x.toOrderHom
      monotone' := by
        intro i j hij
        cases i using Fin.cases with
        | zero => exact Fin.zero_le _
        | succ i =>
          cases j using Fin.cases with
          | zero => simp at hij
          | succ j =>
            apply x.toOrderHom.monotone
            change i.val ≤ j.val
            exact Nat.le_of_succ_le_succ hij }

/--
概要：追加した頂点は標準単体の零点に写る。
方針：先頭追加の定義を計算する。
規約：標準単体の次元は任意。
使われ方：収縮先の頂点の計算。
-/
@[simp] theorem simplexConeZero_zero {k : SimplexCategory} {n : ℕ} (x : k ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x).toOrderHom 0 = 0 := rfl

/--
概要：既存の後続点は元の頂点写像の値に写る。
方針：場合分けの後続点の式を使う。
規約：零点以外の頂点に適用する。
使われ方：面・退化との等式の成分計算。
-/
@[simp] theorem simplexConeZero_succ {k : SimplexCategory} {n : ℕ}
    (x : k ⟶ ⦋n⦌) (i : Fin (k.len + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x).toOrderHom i.succ = x.toOrderHom i := rfl

/--
概要：拡張した射の前合成は、元の前合成への零点の追加と一致する。
方針：零点と後続点で両辺を計算する。
規約：前合成の射の全射性・単射性は不要。
使われ方：像の分解に沿った余分な退化の計算。
-/
theorem simplexConeZero_comp {k l : SimplexCategory} {n : ℕ}
    (θ : k ⟶ l) (x : l ⟶ ⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend θ ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (θ ≫ x) := by
  ext i : 3
  cases i using Fin.cases <;> rfl

/--
概要：最初の面を取ると追加した零点を除いて元の頂点写像になる。
方針：後続点での定義を計算する。
規約：最初の面の番号は零。
使われ方：余分な退化の最初の面の恒等式。
-/
theorem simplexConeZero_δ_zero {k : SimplexCategory} {n : ℕ} (x : k ⟶ ⦋n⦌) :
    SimplexCategory.δ (0 : Fin (k.len + 2)) ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero x = x := by
  ext i : 3
  rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
