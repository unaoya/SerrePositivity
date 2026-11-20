module


public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# 単体の連結成分と単体作用

概要：任意の単体の全ての頂点は同じ連結成分にある。
方針：最初の頂点から他の頂点への辺を単体内に取り、その π₀ の等式を使う。
規約：Mathlib の π₀ のみを用い、高次のホモトピー群を定義しない。
使われ方：KST 式 (2.2) の「π₀ で可逆」の全ての面・退化との両立。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison

open CategoryTheory Opposite SSet
open scoped _root_.Simplicial

/--
概要：単体の i 番目の頂点を取り出す。
方針：[0] から i を選ぶ定数写像を作用させる。
規約：退化単体も含む。KST §2.2 の成分写像の前段。
使われ方：単体の連結成分の定義。
-/
def simplexVertex (X : SSet.{u}) {n : ℕ} (s : X _⦋n⦌) (i : Fin (n + 1)) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op s

/--
概要：単体の最初の頂点と任意の頂点の連結成分は等しい。
方針：最初の頂点から指定した頂点への辺を引き戻す。
規約：Kan 性は不要。KST 式 (2.2) の成分の整合性。
使われ方：全ての単体作用に沿う連結成分の不変性。
-/
theorem simplexVertex_class_eq (X : SSet.{u}) {n : ℕ} (s : X _⦋n⦌)
    (i : Fin (n + 1)) : π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex X s 0) = π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex X s i) := by
  let e := SimplexCategory.mkOfLe 0 i (Fin.zero_le i)
  have h₀ : SimplexCategory.δ (1 : Fin 2) ≫ e = SimplexCategory.const ⦋0⦌ ⦋n⦌ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    fin_cases j
    rfl
  have h₁ : SimplexCategory.δ (0 : Fin 2) ≫ e = SimplexCategory.const ⦋0⦌ ⦋n⦌ i := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    fin_cases j
    rfl
  have h := π₀.sound (Edge.mk' (X.map e.op s))
  change π₀.mk (X.map (SimplexCategory.δ 1).op (X.map e.op s)) =
    π₀.mk (X.map (SimplexCategory.δ 0).op (X.map e.op s)) at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex, ← Functor.map_comp_apply, ← op_comp, h₀, h₁] using h

/--
概要：任意の単体をその連結成分へ送る。
方針：最初の頂点の π₀ を取る。
規約：頂点の選択に依存しないことは `simplexVertex_class_eq`。
使われ方：KST 式 (2.2) の単元成分の逆像。
-/
def simplexClass (X : SSet.{u}) {n : ℕ} (s : X _⦋n⦌) : π₀ X :=
  π₀.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex X s 0)

/--
概要：単体的作用は単体の連結成分を変えない。
方針：引き戻した最初の頂点は元の単体のある頂点である。
規約：全ての面と退化を含む。KST 式 (2.2) の自然性。
使われ方：成分を指定した部分単体集合の構成。
-/
theorem simplexClass_map (X : SSet.{u}) {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : X _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X (X.map f.op s) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X s := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex
  rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex_class_eq X s (f.toOrderHom 0)).symm

/--
概要：零次単体の成分写像は π₀ の商写像である。
方針：[0] 上の定数写像は恒等写像である。
規約：KST 式 (2.2) の零次数の計算。
使われ方：部分モノイドの連結成分の同定。
-/
@[simp] theorem simplexClass_zero (X : SSet.{u}) (s : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass X s = π₀.mk s := by
  simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexClass, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexVertex, SimplexCategory.const_eq_id]

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
