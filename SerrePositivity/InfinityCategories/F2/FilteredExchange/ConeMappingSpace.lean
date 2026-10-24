module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinSliceRestriction
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：指定頂点から元の図式への錐空間と、任意の部分形状への制限を構成する。
方針：slice の頂点射影の fiber と、その射影を保つ制限射を使う。
規約：元の頂点と全単体を保持。使われ方：有限形状の接着による極限空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定頂点を固定した元の図式上の錐空間。 -/
def coneMappingSpace {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) : SSet.{u} :=
  vertexFiber (sliceOverProjection p) x

/-- quasicategory の元の図式の頂点固定の錐空間は Kan 複体。 -/
instance coneMappingSpace_kanComplex {K X : SSet.{u}} [Quasicategory X]
    (p : K ⟶ X) (x : X _⦋0⦌) : KanComplex (coneMappingSpace p x) :=
  vertexFiber_kanComplex (sliceOverProjection p) x

/-- 部分形状への制限は元の錐の頂点を固定した fiber に誘導される。 -/
def coneRestrictionFiberMap {K L X : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    (x : X _⦋0⦌) : coneMappingSpace p x ⟶ coneMappingSpace (i ≫ p) x :=
  vertexFiberMap _ _ (sliceOverRestrict p i) (SerrePositivity.InfinityCategories.kanSliceOverRestrict_projection p i) x

/-- 頂点固定の制限は包含後に元の slice の制限となる。 -/
lemma coneMappingSpace_restrict_ι {K L X : SSet.{u}} (p : K ⟶ X) (i : L ⟶ K)
    (x : X _⦋0⦌) :
    coneRestrictionFiberMap p i x ≫ vertexFiberι (sliceOverProjection (i ≫ p)) x =
      vertexFiberι (sliceOverProjection p) x ≫ sliceOverRestrict p i :=
  vertexFiberMap_ι _ _ _ _ _

end SerrePositivity.InfinityCategories.F2
