module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeTransformationMap
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence

/-!
概要：任意の native な余錐を定値頂点への実際の変換として読み、その円柱を計算する。
方針：余錐空間の頂点に標準比較を適用し、Yoneda 族の全円柱を追跡する。
規約：元の図式と頂点を厳密に保持する。
使われ方：構成済みの全空間余錐と、元の単位を表す変換との整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} {f : K ⟶ X}

/-- 概要：元の余錐を、その頂点を固定した余錐空間の点として表示する。
方針：coslice の零単体に頂点の固定条件を添える。
規約：元の余錐そのもの。使われ方：標準比較の頂点での評価。 -/
def coconeMappingPoint (c : JoinCocone f) : (coconeMappingSpace f c.vertex) _⦋0⦌ :=
  ⟨c, by rw [PinchedHom.constant_zero]; rfl⟩

/-- 概要：native な余錐が定める元の図式から定値頂点への変換の頂点。
方針：標準の全空間の比較を元の余錐の点で評価する。
規約：両端は厳密に f と c.vertex。使われ方：元の単位の変換との比較。 -/
def coconeTransformationVertex (c : JoinCocone f) :
    (intervalMappingSpace (functorVertex f) (functorVertex (SSet.const c.vertex))) _⦋0⦌ :=
  (coconeTransformationMap f c.vertex).app _ (coconeMappingPoint c)

/-- 概要：native な余錐から元の図式と同じ頂点を持つ実際のホモトピーを作る。
方針：変換空間の頂点を関手空間の辺として読み uncurry する。
規約：標的の充填性は不要。使われ方：全空間余錐の単位との照合。 -/
def coconeTransformationHomotopy (c : JoinCocone f) : SSet.Homotopy f (SSet.const c.vertex) :=
  simplicialHomotopyOfFunctorEdge
    (intervalMappingEdgeOfVertex (coconeTransformationVertex c)).toTruncated

/-- 概要：元の余錐の変換の Yoneda 族は元の join の全円柱に厳密に一致する。
方針：全パラメータの比較式を頂点の Yoneda 族へ適用する。
規約：辺の同値類に落とさない。使われ方：fat join の実現の比較ホモトピーとの接続。 -/
lemma coconeTransformationVertex_prism (c : JoinCocone f) :
    constantTransformationPrism (SSet.yonedaEquiv.symm (coconeTransformationVertex c)) =
      joinCylinderMap K (Δ[0] : SSet.{u}) ≫ c.val := by
  rw [coconeTransformationVertex, ← SSet.yonedaEquiv_symm_comp, coconeTransformationMap_prism,
    coconeParameterPrism, SSet.yonedaEquiv_symm_comp]
  change joinCylinderMap K Δ[0] ≫ sliceUnderUncurry (SSet.yonedaEquiv.symm c) = _
  rw [sliceUnderUncurry_yoneda]

end SerrePositivity.InfinityCategories.F2
