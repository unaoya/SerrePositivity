module
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondenceMap
public import SerrePositivity.InfinityCategories.Derived.RoofFiberTransport

/-! # 実屋根 fiber の pinched 同型と元の slice 射影

概要：fiber の全同型は、元の slice への指定射影を厳密に回収する。
方針：pinched 同型を消去し、固定始域輸送と pullback fiber 同型の射影式を使う。
規約：実分母頂点は任意。使われ方：実商比較の fiber 上の鎖写像との照合。
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

omit [Small.{u} D] in
/-- 元の屋根 fiber の同型から slice へ戻すと、元の実射側射影そのもの。 -/
lemma dgRoofCorrespondenceFiberIso_hom_target (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (dgRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      (pinchedHomSliceFiberIso (X := dgNerve A D)
        (Simplex.vertex (dgOverVertexSource A D x σ.val)) (Simplex.vertex y)).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y)))
        (Simplex.vertex (dgOverVertexSource A D x σ.val)) =
    vertexFiberι (dgRoofCorrespondenceProjection A D P x y) σ ≫ pullback.fst _ _ := by
  dsimp only [dgRoofCorrespondenceFiberIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [roofVertexFiberTransport_ι _ (dgRoofCorrespondence_source_vertex A D P x σ)]
  exact cofinalVertexFiberBaseChangeIso_hom_ι _ _ σ

/-- 商側の屋根 fiber の同型も、元の実射側の商 slice 射影を回収する。 -/
lemma dgQuotientRoofCorrespondenceFiberIso_hom_target (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (dgQuotientRoofCorrespondenceFiberIso A D P x y σ).hom ≫
      (pinchedHomSliceFiberIso (X := dgQuotientNerve A D P)
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val)))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))).hom ≫
      vertexFiberι (sliceOverProjection
        ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
          (Simplex.vertex ((DGQuotient.inclusion A D P).obj y))))
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val))) =
    vertexFiberι (dgQuotientRoofCorrespondenceProjection A D P x y) σ ≫
      pullback.fst _ _ := by
  dsimp only [dgQuotientRoofCorrespondenceFiberIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [roofVertexFiberTransport_ι _ (dgQuotientRoofCorrespondence_source_vertex A D P x σ)]
  exact cofinalVertexFiberBaseChangeIso_hom_ι _ _ σ

end SerrePositivity.InfinityCategories
