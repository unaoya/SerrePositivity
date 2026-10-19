module
public import SerrePositivity.InfinityCategories.Derived.DGActualRoofTransport

/-! # 元の商目標まで輸送した実屋根の相対充填データ

概要：実相対充填に、比較・指定輸送・全境界を保持する相対三角形を保持する。
方針：三角形の第二辺を新しい輸送とし、全境界式と元の分母辺への射影を回収する。
規約：存在仮定を構造体に持ち込まない。使われ方：有限同時充填の受入界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実屋根の有限相対充填に保持する、全境界付きの輸送三角形。 -/
structure DGActualRoofTransportedFiller (P : Set D) (x y : D)
    {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s) {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (g : (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((inclusion A D P).obj y)) _⦋n⦌)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌) where
  relative : DGActualRoofRelativeFiller A D P x y R b g t
  triangle : RoofRelativeTransportTriangle (dgQuotientRoofCorrespondenceProjection A D P x y)
    (∂Δ[n]).ι relative.comparison.homotopy relative.target_transport

variable {P : Set D} {x y : D} {s' s : DGClosedVerdierDenominators A D P x} {R : s' ⟶ s}
variable {n : ℕ} {b : (∂Δ[n] : SSet.{max u v}) ⟶
  DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y}
variable {g : (DGNerve.pinchedHom A (QuotientObject D P)
  ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
  ((inclusion A D P).obj y)) _⦋n⦌}
variable {t : (DGNerve.pinchedHom A D
  (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌}
variable (F : DGActualRoofTransportedFiller A D P x y R b g t)

/-- 実充填の商像から元の分母上の元の商単体へ向かう、実際の輸送。 -/
def DGActualRoofTransportedFiller.homotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s' ≫
      dgRoofCorrespondenceMap A D P x y)
    (SSet.yonedaEquiv.symm g ≫ dgQuotientClosedRoofHomInclusion A D P x y s) :=
  F.triangle.homotopy

/-- 輸送の全境界は元の境界の輸送の商像に厳密に一致する。 -/
lemma DGActualRoofTransportedFiller.homotopy_boundary
    (hb : b ≫ pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g) :
    ((∂Δ[n]).ι ▷ Δ[1]) ≫ F.homotopy.h =
      F.relative.boundary_transport.h ≫ dgRoofCorrespondenceMap A D P x y :=
  F.triangle.homotopy_boundary.trans (F.relative.transport_boundary hb)

/-- 輸送は元の指定分母辺を全時間で厳密に被覆する。 -/
lemma DGActualRoofTransportedFiller.homotopy_projection :
    F.homotopy.h ≫ dgQuotientRoofCorrespondenceProjection A D P x y =
      snd (Δ[n] : SSet.{max u v}) Δ[1] ≫
        SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x R).edge :=
  F.triangle.homotopy_over.trans F.relative.target_over

end SerrePositivity.InfinityCategories
