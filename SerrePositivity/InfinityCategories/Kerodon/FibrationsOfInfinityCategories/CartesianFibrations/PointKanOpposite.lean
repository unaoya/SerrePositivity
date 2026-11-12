module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanOppositeCoefficients

/-!
概要：標準一点 Kan 複体の反転は同じ標準一点であることを厳密に確認する。
方針：各次数の順序写像の値域が一元型であることを使う。
規約：一般の Kan 複体と反対複体を同一視する主張ではない。
使われ方：共通 Hom 解像から反転 unstraightening への比較の始点の正規化。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 標準零単体の反転は、対象と全ての単体作用の等式として同じ標準零単体。 -/
lemma stdSimplex_zero_op : (Δ[0] : SSet.{u}).op = Δ[0] := by
  refine CategoryTheory.Functor.ext (F := (Δ[0] : SSet.{u}).op) (G := Δ[0])
    (fun _ => rfl) ?_
  intro n m α
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply ConcreteCategory.hom_ext
  intro s
  apply stdSimplex.ext
  intro i
  exact @Subsingleton.elim (Fin 1) inferInstance _ _

/-- 標準一点 Kan 対象は反転関手で厳密に保存される。 -/
lemma kanObjectOpFunctor_point : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject := by
  have ext {X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} (h : X.obj = Y.obj) : X = Y := by
    cases X
    cases Y
    cases h
    rfl
  exact ext stdSimplex_zero_op

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
