module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleConstantTargetValue
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence

/-!
概要：元の二面の相対比較合成を、同じ二面の全空間作用の比較合成へ移す。
方針：全係数の射影表示と同じ指定同型の像の合成・逆の保存を使う。
規約：共有対角・二面・指定値を保持。使われ方：単位正方形の共役因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u + 1}} {F G L : B ⟶ SpaceInfinity.{u}} {z : SpaceInfinity.{u} _⦋0⦌}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G (SSet.const z)}
  {c : SSet.Homotopy F (SSet.const z)} {s : SSet.Homotopy F L}
  {w : SSet.Homotopy L (SSet.const z)}
  (U : FunctorCompositionTriangle a b c) (D : FunctorCompositionTriangle s w c)

/-- 共有対角を保つ二面の相対比較合成の像は、同じ全空間作用の比較合成そのもの。 -/
lemma functorSquareRelativeComparison_map_constantTarget :
    HEq (VertexIso.map ((functorTriangleRelativeComparison D).symm ≪≫
      functorTriangleRelativeComparison U)
      ((constantUnstraighteningRelativeIso (leftUnstraighteningProjection F) z).hom ≫
        (ihom (leftUnstraightening F)).map (pointedSpaceFiberValueEquivalence z).hom))
      ((functorTriangleConstantTargetActionIso D).symm ≪≫
        functorTriangleConstantTargetActionIso U) := by
  rw [constantUnstraighteningRelativeIso_value_eq_projection]
  unfold functorTriangleConstantTargetActionIso
  rw [functorIso_postcomp_eq_mapIso, functorIso_postcomp_eq_mapIso]
  rw [← vertexIso_map_comp, vertexIso_map_trans, vertexIso_map_symm,
    vertexIso_map_trans, vertexIso_map_symm]
  rfl

end SerrePositivity.InfinityCategories.F2
