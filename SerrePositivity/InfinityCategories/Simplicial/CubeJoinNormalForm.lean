module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.CubeJoinTerm
public import SerrePositivity.InfinityCategories.Simplicial.CubeJoinDetection

/-! # 全出力座標の有限 max 正規形
概要：join を保つ具体的な頂点関数を、出力ごとの一意な定数一・有限 max 表示へ移す。
方針：零頂点の値で場合分けし、真の座標の有限 join による回収式を使う。
規約：生成条件は別に保持し、全正規形が cubical であるとは仮定しない。
使われ方：具体的な cubical 射の表示非依存性と入力 support の順序条件。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction

/-- 全ての出力座標に有限 max 表示を指定したデータ。 -/
abbrev CubeJoinNormalForm (n m : ℕ) := Fin m → CubeJoinTerm n

/-- 元の立方体の全頂点での正規形の評価。 -/
def cubeJoinNormalFormEval {n m : ℕ} (s : CubeJoinNormalForm n m) :
    CubeVertex n → CubeVertex m :=
  fun x j => cubeJoinTermEval (s j) x

/-- 頂点関数から元の出力ごとの定数一・有限 max 表示を回収する。 -/
def cubeJoinNormalFormOfMap {n m : ℕ} (f : CubeVertex n → CubeVertex m) :
    CubeJoinNormalForm n m :=
  fun j => if f ⊥ j = true then none
    else some (Finset.univ.filter (fun i => f (cubeVertexAtom n i) j = true))

/-- join を保つ元の頂点関数は、その同じ有限 max 正規形の評価に一致する。 -/
lemma cubeJoinNormalFormOfMap_eval {n m : ℕ} {f : CubeVertex n → CubeVertex m}
    (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y) (x : CubeVertex n) :
    cubeJoinNormalFormEval (cubeJoinNormalFormOfMap f) x = f x := by
  funext j
  by_cases hz : f ⊥ j = true
  · have hle : f ⊥ ≤ f x := by
      apply sup_eq_right.mp
      simpa only [bot_sup_eq] using (hf ⊥ x).symm
    have hval : f x j = true := by
      have hj := hle j
      rw [hz] at hj
      exact Bool.eq_true_of_true_le hj
    simp [cubeJoinNormalFormEval, cubeJoinNormalFormOfMap, cubeJoinTermEval, hz, hval]
  · have hzero : f ⊥ j = false := by
      cases hb : f ⊥ j <;> simp_all
    have hx := congrFun (cubeJoinMap_eval hf x) j
    simp only [Pi.sup_apply, Finset.sup_apply, hzero] at hx
    change f x j = (⊥ : Bool) ⊔
      (cubeVertexSupport x).sup (fun i => f (cubeVertexAtom n i) j) at hx
    rw [bot_sup_eq] at hx
    dsimp only [cubeJoinNormalFormEval, cubeJoinNormalFormOfMap]
    rw [ite_eq_right hz]
    dsimp only [cubeJoinTermEval]
    rw [hx]
    apply Bool.eq_iff_iff.mpr
    change _ = ⊤ ↔ _ = ⊤
    simp only [Finset.sup_eq_top_iff, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_cubeVertexSupport]
    exact exists_congr (fun i => and_comm)

/-- 全出力の有限 max 正規形は、元の頂点関数で一意に判定される。 -/
lemma cubeJoinNormalFormEval_injective (n m : ℕ) :
    Function.Injective (cubeJoinNormalFormEval (n := n) (m := m)) := by
  intro s t h
  funext j
  apply cubeJoinTermEval_injective n
  funext x
  exact congrFun (congrFun h x) j

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.CubeJoinNormalForm := _root_.SerrePositivity.InfinityCategories.Simplicial.CubeJoinNormalForm

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormEval := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormEval_injective := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval_injective

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormOfMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormOfMap := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormOfMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormOfMap_eval := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormOfMap_eval

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormEval.eq_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormEval.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.cubeJoinNormalFormOfMap.eq_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.cubeJoinNormalFormOfMap.eq_1
