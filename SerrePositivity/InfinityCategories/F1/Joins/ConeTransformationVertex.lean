module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeTransformationMap
public import SerrePositivity.InfinityCategories.F1.Joins.ConeVariablePrism
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeMappingSpan

/-!
概要：同じ native な錐の頂点を定値始域の変換へ送り、その全円柱を計算する。
方針：元の slice fiber の点に標準比較を作用させ、同じ全族の円柱を追跡する。
規約：元の錐・頂点・図式を保持する。
使われ方：全 Hom 三角形の第二辺と、全切断の恒等射を表す変換との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X T : SSet.{u}} {f : K ⟶ X}

/-- 元の錐を、同じ頂点の native な錐の関手空間の点として表示する。 -/
def coneMappingPoint (c : JoinCone f) : (fixedApexConeFamily f c.vertex) _⦋0⦌ :=
  (coneVertexFiberFamilyMap f c.vertex).app (Opposite.op ⦋0⦌) (coneVertexFiberPoint c)

/-- 元の錐の点が与える、同じ定値始域から元の図式への変換。 -/
def coneTransformationVertex (c : JoinCone f) :
    (intervalMappingSpace (functorVertex (SSet.const c.vertex)) (functorVertex f)) _⦋0⦌ :=
  (coneTransformationMap f c.vertex).app (Opposite.op ⦋0⦌) (coneMappingPoint c)

/-- 元の錐の変換を、同じ頂点・図式を両端に持つ円柱として読む。 -/
def coneTransformationHomotopy (c : JoinCone f) : SSet.Homotopy (SSet.const c.vertex) f :=
  simplicialHomotopyOfFunctorEdge
    (intervalMappingEdgeOfVertex (coneTransformationVertex c)).toTruncated

/-- 元の錐の定値変換の円柱は、同じ元の錐の定値族の全円柱。 -/
lemma coneTransformationVertex_const_prism (c : JoinCone f) :
    sourceConstantTransformationPrism (SSet.const (coneTransformationVertex c) : T ⟶ _) =
      coneVariablePrism (SSet.const c : T ⟶ sliceOver f) := by
  rw [show (SSet.const (coneTransformationVertex c) : T ⟶ _) =
      SSet.const (coneMappingPoint c) ≫ coneTransformationMap f c.vertex from
        (SSet.const_comp _ _).symm, coneTransformationMap_prism]
  rw [show (SSet.const (coneMappingPoint c) : T ⟶ _) =
      SSet.const (coneVertexFiberPoint c) ≫ coneVertexFiberFamilyMap f c.vertex from
        (SSet.const_comp _ _).symm, ← coneVariablePrism_fixed, SSet.const_comp]
  rfl

/-- 頂点の Yoneda 族としての変換も、元の錐の同じ全円柱を厳密に回収する。 -/
lemma coneTransformationVertex_prism (c : JoinCone f) :
    sourceConstantTransformationPrism (SSet.yonedaEquiv.symm (coneTransformationVertex c)) =
      fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ coneCylinderMap K ≫ c.val := by
  rw [coneTransformationVertex, ← SSet.yonedaEquiv_symm_comp, coneTransformationMap_prism]
  rw [show SSet.yonedaEquiv.symm (coneMappingPoint c) =
      SSet.yonedaEquiv.symm (coneVertexFiberPoint c) ≫ coneVertexFiberFamilyMap f c.vertex from
        (SSet.yonedaEquiv_symm_comp _ _).symm, ← coneVariablePrism_fixed,
    SSet.yonedaEquiv_symm_comp]
  change coneVariablePrism (SSet.yonedaEquiv.symm c) = _
  rw [coneVariablePrism, sliceConeFamilyUncurry_vertex, whiskerRight_fst_assoc]

end SerrePositivity.InfinityCategories
