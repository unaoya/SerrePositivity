module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFourLastHornCochainFiller

/-! # 実最後外ホーンの二未知微分方程式の解

概要：指定ホーンから回収した二つの型付き cochain と微分式を、実充填へ渡す一つの解に束ねる。
方針：既知対象族を固定して Q・A の式を保持し、構成した四単体の米田表示を返す。
規約：解の存在は構造のフィールドから推論しない。使われ方：分母消去の代数的解の受入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 実四次最後外ホーンから回収した二未知 cochain の型付き解。 -/
structure DGFourLastHornSolution (σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) where
  Q : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 3) (-2)
  differential_Q : differential A Q = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornMissingResidual σ
  a : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 4) (-3)
  differential_a : differential A a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornTopResidual σ +
    compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom 3 4 (by decide)) Q (by decide)

variable {σ : (Λ[4, 4] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D} (S : DGFourLastHornSolution σ)

/-- 型付きの解から元の指定四面を持つ実四単体へ。 -/
def DGFourLastHornSolution.simplex : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 4 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFillerSimplex σ S.Q S.differential_Q S.a S.differential_a

/-- 型付きの解から元のホーン全体を延長する実写像へ。 -/
def DGFourLastHornSolution.extension : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm S.simplex

/-- 解から得た実写像は元の指定ホーン全体を厳密に延長する。 -/
lemma DGFourLastHornSolution.fac : (horn 4 4).ι ≫ S.extension = σ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornFiller_extension σ S.Q S.differential_Q S.a S.differential_a).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
