module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGActualRoofTransport

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 実屋根の有限相対充填に保持する、全境界付きの輸送三角形。 -/
structure DGActualRoofTransportedFiller (P : Set D) (x y : D)
    {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} (R : s' ⟶ s) {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
      ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋n⦌)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌) where
  relative : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofRelativeFiller A D P x y R b g t
  triangle : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
    (∂Δ[n]).ι relative.comparison.homotopy relative.target_transport

variable {P : Set D} {x y : D} {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} {R : s' ⟶ s}
variable {n : ℕ} {b : (∂Δ[n] : SSet.{max u v}) ⟶
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y}
variable {g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋n⦌}
variable {t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s'.obj.left) y) _⦋n⦌}
variable (F : DGActualRoofTransportedFiller A D P x y R b g t)

/-- 実充填の商像から元の分母上の元の商単体へ向かう、実際の輸送。 -/
def DGActualRoofTransportedFiller.homotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s' ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (SSet.yonedaEquiv.symm g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) :=
  F.triangle.homotopy

/-- 輸送の全境界は元の境界の輸送の商像に厳密に一致する。 -/
lemma DGActualRoofTransportedFiller.homotopy_boundary
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g) :
    ((∂Δ[n]).ι ▷ Δ[1]) ≫ F.homotopy.h =
      F.relative.boundary_transport.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y :=
  F.triangle.homotopy_boundary.trans (F.relative.transport_boundary hb)

/-- 輸送は元の指定分母辺を全時間で厳密に被覆する。 -/
lemma DGActualRoofTransportedFiller.homotopy_projection :
    F.homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      snd (Δ[n] : SSet.{max u v}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge A D P x R).edge :=
  F.triangle.homotopy_over.trans F.relative.target_over

end SerrePositivity.InfinityCategories.Project.DerivedCategories
