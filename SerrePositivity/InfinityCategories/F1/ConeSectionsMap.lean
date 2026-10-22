module

public import SerrePositivity.InfinityCategories.F1.CoherentConstantSourceComparison
public import SerrePositivity.InfinityCategories.F1.ConeTransformationPointAt

/-!
概要：元の錐の標準変換を、指定 fiber から全切断への実際の射として表示する。
方針：定値始域比較の同じ頂点を内部 Hom の頂点の全単射で読む。
規約：錐・図式・頂点の等式を保持する。
使われ方：全切断の恒等射比較を全 Hom の後合成へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の錐が定める、指定 fiber から同じ図式の全切断への射。 -/
def coneSectionsMapAt (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌) (hv : c.vertex = z) :
    vertexFiber pointedSpaceProjection z ⟶
      HomotopyLimits.simplicialSections (leftUnstraighteningProjection F) :=
  (functorVertexEquiv _ _).symm ((coherentConstantSourceMap F z).app (Opposite.op ⦋0⦌)
    (coneTransformationPointAt c z hv))

/-- 同じ実際の射の頂点は、元の標準変換の比較像そのもの。 -/
lemma coneSectionsMapAt_vertex (c : JoinCone F) (z : SpaceInfinity.{u} _⦋0⦌)
    (hv : c.vertex = z) :
    functorVertex (coneSectionsMapAt c z hv) =
      (coherentConstantSourceMap F z).app (Opposite.op ⦋0⦌)
        (coneTransformationPointAt c z hv) :=
  (functorVertexEquiv _ _).apply_symm_apply _

/-- 元の錐の頂点を変更しない標準の全切断写像。 -/
def coneSectionsMap (c : JoinCone F) := coneSectionsMapAt c c.vertex rfl

end SerrePositivity.InfinityCategories
