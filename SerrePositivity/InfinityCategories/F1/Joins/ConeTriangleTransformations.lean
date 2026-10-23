module

public import SerrePositivity.InfinityCategories.F1.Joins.ConePointHomTriangle
public import SerrePositivity.InfinityCategories.F1.Joins.ConeTransformationVertex
public import SerrePositivity.InfinityCategories.F2.ConstantDiagramTransformation

/-!
概要：元の錐の全 Hom 三角形の二つの短辺を、同じ定値始域の変換の全族と照合する。
方針：標準 Hom の辺と、同じ指定錐の標準変換の円柱を座標で戻す。
規約：全 Hom・元の指定錐と元の二変換を保持する。
使われ方：unstraightening の合成則の二短辺への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の全 Hom の辺を、同じ両頂点の定値図式間の変換として表示する。 -/
def conePointHomFirstTransformation (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :=
  F2.constantDiagramTransformation B (pinchedHomToIntervalMappingSpace z c.vertex)

/-- 元の三角形の第一辺は、元の Hom の定値図式間の変換そのもの。 -/
lemma conePointHomTriangle_first_transformation
    (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ pinchedHom z c.vertex)) ≫ conePointHomTriangle c z =
      coherentTransformationFamilyDiagram (conePointHomFirstTransformation c z) := by
  rw [conePointHomTriangle_first, conePointHomFirstTransformation,
    F2.constantDiagramTransformation_diagram]

/-- 元の三角形の第二辺は、同じ指定錐の標準変換の定値族。 -/
lemma conePointHomTriangle_second_transformation
    (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) :
    (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ pinchedHom z c.vertex)) ≫ conePointHomTriangle c z =
      coherentTransformationFamilyDiagram
        (SSet.const (coneTransformationVertex c) : pinchedHom z c.vertex ⟶ _) := by
  rw [conePointHomTriangle_second, ← coneTransformationVertex_const_prism]
  apply SSet.hom_ext
  intro n
  rfl

end SerrePositivity.InfinityCategories
