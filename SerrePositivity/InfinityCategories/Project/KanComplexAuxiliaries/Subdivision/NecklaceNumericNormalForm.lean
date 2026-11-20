module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Subdivision.NecklaceNumericMap
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CubeOrderedNormalFormGenerated

/-! # 元の necklace 写像の数値座標における順序つき max 表示
概要：joint の像を定数一、残りを同じ元の頂点ファイバーの有限 max として表す。
方針：元の全座標の真偽式と、右端列挙によるファイバーの順序分離を使う。
規約：表示の評価は同じ元の写像。使われ方：全 necklace 射の実際の cubical 生成条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の出力座標が始域の joint の像に入るという条件。 -/
def necklaceJointHits {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) (j : Fin U.down.dimension) : Prop :=
  ∃ a : T.down.Vertex, a.val ∈ T.down.joints ∧
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f a = (U.down.nonjointCoordinate j).val

/-- 元の necklace 射の右端からの数値座標の有限 max 表示。 -/
def necklaceNumericNormalForm {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeJoinNormalForm T.down.dimension U.down.dimension := by
  classical
  exact fun j => if _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceJointHits f j then none else
    some (Finset.univ.filter (fun i => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate i).val =
      (U.down.nonjointCoordinate j).val))

/-- 元の表示の support は、joint 像でない出力の同じ数値ファイバー。 -/
lemma mem_necklaceNumericNormalForm_support {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    (i : Fin T.down.dimension) (j : Fin U.down.dimension) :
    i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm f) j ↔
      ¬ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceJointHits f j ∧ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate i).val =
        (U.down.nonjointCoordinate j).val := by
  classical
  by_cases h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceJointHits f j <;>
    simp [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport, h]

/-- 元の全出力の有限 max 表示は、入力 support が出力順に厳密に並ぶ。 -/
lemma necklaceNumericNormalForm_ordered {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U)
    {j k : Fin U.down.dimension} (hjk : j < k) {i l : Fin T.down.dimension}
    (hi : i ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm f) j)
    (hl : l ∈ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeJoinNormalFormSupport (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm f) k) : i < l := by
  have hi' := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_necklaceNumericNormalForm_support f i j).1 hi
  have hl' := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mem_necklaceNumericNormalForm_support f l k).1 hl
  have hu := (U.down.nonjointCoordinate_lt k j).2 hjk
  have hh : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate l).val <
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate i).val := by
    rw [hl'.2, hi'.2]
    exact hu
  exact (T.down.nonjointCoordinate_lt l i).1
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap_orderedFibers f _ _ hh)

/-- 元の有限 max 表示は、同じ necklace 射の全数値頂点作用を厳密に回収する。 -/
lemma necklaceNumericNormalForm_eval {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm f) = _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f := by
  classical
  funext x j
  apply Bool.eq_iff_iff.mpr
  rw [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap_coordinate]
  change _ ↔ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceJointHits f j ∨ ∃ i, x i = true ∧
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceVertexMap f (T.down.nonjointCoordinate i).val = (U.down.nonjointCoordinate j).val
  by_cases h : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceJointHits f j
  · simp [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm, h, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval]
  · simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinNormalFormEval, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm,
      h, ite_false, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.cubeJoinTermEval, false_or]
    change _ = (⊤ : Bool) ↔ _
    rw [Finset.sup_eq_top_iff]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr (fun i => and_comm)

/-- 元の全 necklace 射の数値頂点作用は、既存の cubical 生成射の合成。 -/
lemma necklaceNumericMap_generated {T U : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Necklace.{u}} (f : T ⟶ U) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.CubeMapGenerated (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceNumericMap f) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm_eval f]
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeOrderedNormalForm_generated (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm f)
    (by
      intro j k hjk i l hi hl
      exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.necklaceNumericNormalForm_ordered f hjk hi hl)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
