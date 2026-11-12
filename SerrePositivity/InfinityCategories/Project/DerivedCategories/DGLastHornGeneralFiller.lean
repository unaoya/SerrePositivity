module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornGeneralCochains
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBoundaryTopCompletion

/-! # 一般の二未知 cochain 解から実最後外ホーン全体を充填する

概要：欠面 Q と最上位 A の型付き微分式から、次元 n+2 の実単体と指定全面の延長を構成。
方針：Q 挿入後の全真部分方程式を使い、最上位成分だけを A で完成する。
規約：解の存在は入力として明示する。使われ方：一般残差 cone の原始元から実充填へ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}

/-- 一般最後外ホーンから回収した二未知の型付き解。 -/
structure DGGeneralLastHornSolution
    (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) (-(n : ℤ))
  differential_Q : differential A Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornMissingResidual σ
  a : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) (-(n : ℤ) - 1)
  differential_a : differential A a = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ Q).rhs Finset.univ
    0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n)

variable {σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D}
variable (S : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGGeneralLastHornSolution σ)

/-- 二未知解から得る、指定ホーンの全ての面を保つ実単体。 -/
def DGGeneralLastHornSolution.simplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 2) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompleteTopSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ S.Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_properEquations σ S.Q S.differential_Q)
    0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n) S.a S.differential_a

/-- 一般解から得た実単体は、元の指定面を全て厳密に保つ。 -/
lemma DGGeneralLastHornSolution.simplex_face (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ j S.simplex = σ.app _ (horn.face (Fin.last (n + 2)) j hj) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompleteTopSimplex_pullback_face (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData σ S.Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_properEquations σ S.Q S.differential_Q)
    0 (Fin.last (n + 2)) (-(n : ℤ) - 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_two n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_min n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_max n) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornTop_degree n)
      S.a S.differential_a j).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornQData_face σ S.Q j hj)

/-- 一般解から得る、元のホーン全体を延長する実写像。 -/
def DGGeneralLastHornSolution.extension : Δ[n + 2] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm S.simplex

/-- 実写像は元の指定ホーン全体の延長である。 -/
lemma DGGeneralLastHornSolution.fac :
    (horn (n + 2) (Fin.last (n + 2))).ι ≫ S.extension = σ := by
  apply SSet.horn.hom_ext
  intro j hj
  rw [← S.simplex_face j hj, NatTrans.comp_app]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
