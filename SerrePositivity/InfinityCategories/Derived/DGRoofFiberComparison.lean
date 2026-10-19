module
public import SerrePositivity.InfinityCategories.Derived.DGRoofFiberProjection
public import SerrePositivity.InfinityCategories.Derived.DGQuotientPinchedSlice
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-! # 実屋根の商比較の全 fiber と Hom 鎖写像の一致

概要：任意の実分母頂点の fiber 上の商比較は、元の商の全 Hom 鎖写像の pinched 作用。
方針：元の実 target slice への単射な包含後で比較し、両 fiber 同型の射影公式を使う。
規約：単体集合の射の厳密な等式。使われ方：有限相対充填の実屋根への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の実屋根比較が、同じ指定実分母頂点の fiber に誘導する写像。 -/
def dgRoofCorrespondenceFiberMap (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    vertexFiber (dgRoofCorrespondenceProjection A D P x y) σ ⟶
      vertexFiber (dgQuotientRoofCorrespondenceProjection A D P x y) σ :=
  vertexFiberMap _ _ (dgRoofCorrespondenceMap A D P x y)
    (dgRoofCorrespondenceMap_projection A D P x y) σ

/-- fiber 上の比較は、元の実屋根への包含と厳密に可換。 -/
lemma dgRoofCorrespondenceFiberMap_ι (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofCorrespondenceFiberMap A D P x y σ ≫
      vertexFiberι (dgQuotientRoofCorrespondenceProjection A D P x y) σ =
    vertexFiberι (dgRoofCorrespondenceProjection A D P x y) σ ≫
      dgRoofCorrespondenceMap A D P x y :=
  vertexFiberMap_ι _ _ _ _ σ

/-- 実屋根の商比較の全 fiber は、元の商の Hom 鎖写像の実 pinched 写像と一致。 -/
theorem dgRoofCorrespondenceFiberMap_comparison (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    dgRoofCorrespondenceFiberMap A D P x y σ ≫
      (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom =
    (dgRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      pinchedHomChainMap ((DGQuotient.inclusion A D P).map
        (dgOverVertexSource A D x σ.val) y) := by
  let q := dgOverVertexSource A D x σ.val
  let j := (pinchedHomSliceFiberIso (X := dgQuotientNerve A D P)
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj q))
    (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
    vertexFiberι (sliceOverProjection
      ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
      (Simplex.vertex ((DGQuotient.inclusion A D P).obj q))
  have : Mono j := by dsimp only [j]; infer_instance
  apply (cancel_mono j).mp
  dsimp only [j]
  simp only [Category.assoc]
  rw [dgQuotientRoofCorrespondenceFiberIso_hom_target]
  rw [← Category.assoc (dgRoofCorrespondenceFiberMap A D P x y σ),
    dgRoofCorrespondenceFiberMap_ι, Category.assoc, dgRoofCorrespondenceMap_target]
  rw [← Category.assoc (vertexFiberι (dgRoofCorrespondenceProjection A D P x y) σ),
    ← dgRoofCorrespondenceFiberIso_hom_target]
  simp only [Category.assoc]
  rw [dgQuotientTargetSliceMap_pinched]

/-- 両 fiber 同型で共役した実商比較は、元の全 Hom 鎖写像そのもの。 -/
lemma dgRoofCorrespondenceFiberMap_conjugate (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (dgRoofCorrespondenceFiberIso A D P x y σ).inv ≫
      dgRoofCorrespondenceFiberMap A D P x y σ ≫
      (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom =
    pinchedHomChainMap ((DGQuotient.inclusion A D P).map
      (dgOverVertexSource A D x σ.val) y) := by
  rw [dgRoofCorrespondenceFiberMap_comparison, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories
