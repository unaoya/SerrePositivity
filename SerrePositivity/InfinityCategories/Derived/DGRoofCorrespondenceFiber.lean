module
public import SerrePositivity.InfinityCategories.Derived.DGRoofCorrespondence
public import SerrePositivity.InfinityCategories.Derived.DGOverVertexInverse
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange

/-! # 実屋根の右ファイブレーションの全 fiber と実 pinched Hom

概要：任意の実分母頂点上の元の屋根と商側屋根の fiber を、実 pinched Hom と同型にする。
方針：pullback の fiber 同型と slice fiber の pinched 同型で、元の始域を照合する。
規約：全次元の厳密な単体集合同型。使われ方：係数の有限相対充填の実屋根への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 実分母頂点の始域の実零単体は、回収した元の対象の頂点。 -/
lemma dgRoofCorrespondence_source_vertex (P : Set D) (x : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) σ =
      Simplex.vertex (dgOverVertexSource A D x σ.val) := by
  apply (dgNerve.vertexEquiv A D).injective
  rfl

/-- 任意の実分母頂点上の元の屋根 fiber は、その始域からの実 pinched Hom。 -/
def dgRoofCorrespondenceFiberIso (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    vertexFiber (dgRoofCorrespondenceProjection A D P x y) σ ≅
      DGNerve.pinchedHom A D (dgOverVertexSource A D x σ.val) y :=
  cofinalVertexFiberBaseChangeIso _ _ σ ≪≫
    eqToIso (congrArg (vertexFiber (sliceOverProjection
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex y))))
        (dgRoofCorrespondence_source_vertex A D P x σ)) ≪≫
    (pinchedHomSliceFiberIso _ _).symm

/-- 商側の実分母の始域頂点も、同じ元の対象の商像の頂点。 -/
lemma dgQuotientRoofCorrespondence_source_vertex (P : Set D) (x : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P).app
      (Opposite.op ⦋0⦌) σ =
      Simplex.vertex ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val)) := by
  change (dgQuotientNerveProjection A D P).app _
    ((dgVerdierOverSource A D P x).app (Opposite.op ⦋0⦌) σ) = _
  rw [dgRoofCorrespondence_source_vertex]
  apply (dgNerve.vertexEquiv A (DGQuotient.QuotientObject D P)).injective
  rfl

/-- 任意の同じ実分母頂点上の商側屋根 fiber は、元の始域の商像からの実 pinched Hom。 -/
def dgQuotientRoofCorrespondenceFiberIso (P : Set D) (x y : D)
    (σ : (dgVerdierOver A D P x : SSet) _⦋0⦌) :
    vertexFiber (dgQuotientRoofCorrespondenceProjection A D P x y) σ ≅
      DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
        ((DGQuotient.inclusion A D P).obj (dgOverVertexSource A D x σ.val))
        ((DGQuotient.inclusion A D P).obj y) :=
  cofinalVertexFiberBaseChangeIso _ _ σ ≪≫
    eqToIso (congrArg (vertexFiber (sliceOverProjection
      ((SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
        (Simplex.vertex ((DGQuotient.inclusion A D P).obj y)))))
          (dgQuotientRoofCorrespondence_source_vertex A D P x σ)) ≪≫
    (pinchedHomSliceFiberIso _ _).symm

end SerrePositivity.InfinityCategories
