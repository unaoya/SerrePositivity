module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeWordRealization
public import Mathlib.Order.Preorder.Finite

/-! # 順序を保つ座標選択と一座標削除による分解
概要：使用しない入力座標を一つ飛ばし、元の順序を保つ選択を低い次元へ移す。
方針：Fin.succAbove の像の特徴づけから下の添字を回収する。
規約：空の入力・出力も含む。使われ方：未使用入力を削除する正規化の第一工程。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction

/-- 元の指定した入力座標を元の順で選択する頂点関数。 -/
def cubeCoordinateSelect {n m : ℕ} (e : Fin m → Fin n) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  fun x j => x (e j)

/-- 元の選択に使わない一座標を飛ばした、低次元の選択添字。 -/
def cubeCoordinateLower {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) : Fin m → Fin n :=
  fun j => Classical.choose (Fin.exists_succAbove_eq (hp j))

/-- 低次元の選択添字を元の一座標削除の埋め込みで回収する。 -/
lemma cubeCoordinateLower_spec {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) (j : Fin m) :
    p.succAbove (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower e p hp j) = e j :=
  Classical.choose_spec (Fin.exists_succAbove_eq (hp j))

/-- 元の選択添字の厳密な順序は、未使用座標を飛ばしても保たれる。 -/
lemma cubeCoordinateLower_strictMono {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) (he : StrictMono e) :
    StrictMono (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower e p hp) := by
  intro i j hij
  apply (Fin.strictMono_succAbove p).lt_iff_lt.mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_spec, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_spec]
  exact he hij

/-- 元の選択関数は、一座標削除と低次元の選択との元の関数としての合成。 -/
lemma cubeCoordinateSelect_lower {n m : ℕ} (e : Fin m → Fin (n + 1))
    (p : Fin (n + 1)) (hp : ∀ j, e j ≠ p) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect e =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower e p hp) ∘ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexDegeneracy n p := by
  funext x j
  exact congrArg x (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_spec e p hp j).symm

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateLower := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateLower_spec := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateLower_strictMono := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower_strictMono

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateSelect_lower := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateSelect_lower

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeCoordinateLower._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeCoordinateLower._proof_1
