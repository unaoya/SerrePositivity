module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-!
分割で生成：docstring を書き直すこと
 # Suspension と loop の図式の族

概要：二つの零角を持つ普遍四角形を、正方形からの関手 ∞ 圏の全部分圏に束ねる。
方針：頂点条件で普遍性を課し、左右の対角の評価を単体的な射として使う。
規約：評価の同値性はここではまだ主張しない。使われ方：S3 の h C 上の関手の構成。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 概要：正方形の関手の頂点を、正方形からの実際の射へ戻す。
方針：関手頂点の標準同値を逆に使う。
規約：正方形の二つの座標の順序を保つ。使われ方：普遍四角形の頂点条件。 -/
def squareDiagram {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Δ[1] ⊗ Δ[1] ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm v

/-- 概要：suspension 図式の頂点条件は二つの零角と押し出し性。
方針：図式の実際の四角形に条件を課す。
規約：対角の頂点は自由に動く。使われ方：suspension 図式の全部分圏。 -/
def IsSuspensionDiagramVertex {X : SSet.{u}}
    (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (squareDiagram v) 0 1) ∧
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (squareDiagram v) 1 0) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (squareDiagram v)

/-- 概要：全 suspension 図式からなる関手 ∞ 圏の全部分単体集合。
方針：各頂点で零角と押し出し性を課す。
規約：高次単体は実際の四角形の族。使われ方：suspension の関手性。 -/
def suspensionDiagrams (X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)
    IsSuspensionDiagramVertex : SSet.{u})

/-- 概要：suspension 図式を指定した角で評価する単体的な射。
方針：全部分圏の包含と関手の評価を合成する。
規約：全ての高次単体に自然。使われ方：Σ の始点・終点の関手。 -/
def suspensionDiagramEvaluation (X : SSet.{u}) (i j : Fin 2) : suspensionDiagrams X ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsSuspensionDiagramVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
