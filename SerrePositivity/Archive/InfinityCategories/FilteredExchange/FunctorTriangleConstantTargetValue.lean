module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantUnstraighteningRelativeProjection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleRelativeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningTriangleVertex
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：定値標的の相対三角形比較を、同じ全空間作用の三角形比較へ値まで移す。
方針：相対 Hom 同型の全係数の射影表示と指定同型の合成則を使う。
規約：元の全二単体と指定値を保持。使われ方：上下作用比較を同じ値で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G : B ⟶ SpaceInfinity.{u}} {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G (SSet.const z)}
  {c : SSet.Homotopy F (SSet.const z)} (T : FunctorCompositionTriangle a b c)

/-- 元の定値標的への全三角形の比較を、同じ fiber 射影と値の比較で写す。 -/
def functorTriangleConstantTargetActionIso :=
  FunctorIso.postcomp (unstraighteningTriangleVertexIso F G (SSet.const z)
    (coherentVertexOfHomotopy a) (coherentVertexOfHomotopy b) (coherentVertexOfHomotopy c)
    (coherentTriangleOfFunctorTriangle T).diagram (coherentTriangleOfFunctorTriangle T).first
    (coherentTriangleOfFunctorTriangle T).second (coherentTriangleOfFunctorTriangle T).long)
    (constantUnstraighteningFiberProjection B z ≫ (pointedSpaceFiberValueEquivalence z).hom)

/-- 相対比較の元の値への像は、同じ全三角形の全空間比較を射影した同じ指定値。 -/
lemma functorTriangleRelativeComparison_map_constantTarget :
    HEq (VertexIso.map (functorTriangleRelativeComparison T)
      ((constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
        (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom))
      (functorTriangleConstantTargetActionIso T) := by
  unfold functorTriangleConstantTargetActionIso
  rw [constantUnstraighteningRelativeIso_value_eq_projection, functorIso_postcomp_eq_mapIso]
  exact (heq_of_eq (vertexIso_map_comp (functorTriangleRelativeComparison T) _ _)).symm

end SerrePositivity.InfinityCategories.F2
