module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeJoinTerm
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Cubes.CubeJoinDetection

/-! # 全出力座標の有限 max 正規形
概要：join を保つ具体的な頂点関数を、出力ごとの一意な定数一・有限 max 表示へ移す。
方針：零頂点の値で場合分けし、真の座標の有限 join による回収式を使う。
規約：生成条件は別に保持し、全正規形が cubical であるとは仮定しない。
使われ方：具体的な cubical 射の表示非依存性と入力 support の順序条件。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 全ての出力座標に有限 max 表示を指定したデータ。 -/
abbrev CubeJoinNormalForm (n m : ℕ) := Fin m → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinTerm n

/-- 元の立方体の全頂点での正規形の評価。 -/
def cubeJoinNormalFormEval {n m : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m :=
  fun x j => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval (s j) x

/-- 頂点関数から元の出力ごとの定数一・有限 max 表示を回収する。 -/
def cubeJoinNormalFormOfMap {n m : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm n m :=
  fun j => if f ⊥ j = true then none
    else some (Finset.univ.filter (fun i => f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j = true))

/-- join を保つ元の頂点関数は、その同じ有限 max 正規形の評価に一致する。 -/
lemma cubeJoinNormalFormOfMap_eval {n m : ℕ} {f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n → _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (x : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeVertex n) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap f) x = f x := by
  funext j
  by_cases hz : f ⊥ j = true
  · have hle : f ⊥ ≤ f x := by
      apply sup_eq_right.mp
      simpa only [bot_sup_eq] using (hf ⊥ x).symm
    have hval : f x j = true := by
      have hj := hle j
      rw [hz] at hj
      exact Bool.eq_true_of_true_le hj
    simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval, hz, hval]
  · have hzero : f ⊥ j = false := by
      cases hb : f ⊥ j <;> simp_all
    have hx := congrFun (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinMap_eval hf x) j
    simp only [Pi.sup_apply, Finset.sup_apply, hzero] at hx
    change f x j = (⊥ : Bool) ⊔
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexSupport x).sup (fun i => f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeVertexAtom n i) j) at hx
    rw [bot_sup_eq] at hx
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormOfMap]
    rw [ite_eq_right hz]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval]
    rw [hx]
    apply Bool.eq_iff_iff.mpr
    change _ = ⊤ ↔ _ = ⊤
    simp only [Finset.sup_eq_top_iff, Finset.mem_filter, Finset.mem_univ, true_and,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.mem_cubeVertexSupport]
    exact exists_congr (fun i => and_comm)

/-- 全出力の有限 max 正規形は、元の頂点関数で一意に判定される。 -/
lemma cubeJoinNormalFormEval_injective (n m : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (n := n) (m := m)) := by
  intro s t h
  funext j
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval_injective n
  funext x
  exact congrFun (congrFun h x) j

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
