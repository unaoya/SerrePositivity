module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeEquations
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
/-!
概要：dg nerve の全単体と反対 dg 模型の全単体の、符号付き反転の全単射。
方針：全 HA 方程式の保存と、二回反転の実全成分の復元を接続する。
規約：単体次数ごとの比較。全単体作用との自然性は別途証明する。
使われ方：β5 の dg 反対模型と単体的反対圏の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {n : ℕ}
/-- 反対模型の同じ単体を元の dg 圏へ戻す実操作。 -/
def unopSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Dᵒᵖ n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex s).map (dgDoubleUnop R D)
/-- 逆向き単体の実成分は、同じ符号付き逆データと厳密に一致する。 -/
lemma unopSimplex_data (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Dᵒᵖ n) :
    (unopSimplex s).toSimplexData = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.unop s.toSimplexData := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    rfl
/-- 元の実単体を反転して戻すと、同じ全単体へ厳密に戻る。 -/
@[simp] lemma unop_opSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n) : unopSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [unopSimplex_data]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.unop_op s.toSimplexData
/-- 反対模型の実単体も同じ全成分へ厳密に戻る。 -/
@[simp] lemma op_unopSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Dᵒᵖ n) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (unopSimplex s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op (unopSimplex s).toSimplexData = s.toSimplexData
  rw [unopSimplex_data]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.op_unop s.toSimplexData
/-- 各次元の実全単体の、微分方程式を保つ反転の全単射。 -/
def simplexEquiv (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R Dᵒᵖ n where
  toFun := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex
  invFun := unopSimplex
  left_inv := unop_opSimplex
  right_inv := op_unopSimplex
end SerrePositivity.InfinityCategories.Project.DerivedCategories
