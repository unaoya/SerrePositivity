module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofRelativeFiller
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientRoofLocallyConstant
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportHomotopy

/-! # 実屋根の相対充填を元の指定商目標へ輸送する

概要：境界固定比較と指定輸送を相対三角形へ充填し、実充填から元の商目標への辺族を得る。
方針：商屋根の左ファイブレーション性と、比較の定値分母・二輸送の境界整合性を使う。
規約：全境界・全時刻と元の指定分母辺を保持。使われ方：β3 の有限相対持ち上げ。
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
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) (hP : localKFlat A D P) (x y : D)
variable {s' s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedVerdierDenominators A D P x} {R : s' ⟶ s} {n : ℕ}
variable {b : (∂Δ[n] : SSet.{max u v}) ⟶
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y}
variable {g : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A (QuotientObject D P)
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left))
  ((_root_.SerrePositivity.DifferentialGraded.DGQuotient.inclusion A D P).obj y)) _⦋n⦌}
variable {t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D
  (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s'.obj.left) y) _⦋n⦌}
variable (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGActualRoofRelativeFiller A D P x y R b g t)

include hP in
/-- 比較と指定輸送は、境界の退化三角形と底三角形を保持して同時に充填できる。 -/
lemma DGActualRoofRelativeFiller.transportTriangle_nonempty :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
      (∂Δ[n]).ι F.comparison.homotopy F.target_transport) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection_leftFibration A D P hP x y
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRelativeTransportTriangle_nonempty _ _ _ _ F.comparison.boundary
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofHomotopy_over_constant F.comparison.homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorVertex A D P x s') F.comparison_over)

/-- 全指定辺・全境界と分母射影を保持する実屋根内の相対三角形。 -/
def DGActualRoofRelativeFiller.transportTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofRelativeTransportTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y)
      (∂Δ[n]).ι F.comparison.homotopy F.target_transport :=
  Classical.choice (F.transportTriangle_nonempty A D P hP x y)

/-- 細分後の実充填の商像を、元の分母上の元の商目標へ直接結ぶ実輸送。 -/
def DGActualRoofRelativeFiller.transportHomotopy : SSet.Homotopy
    (SSet.yonedaEquiv.symm t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedRoofHomInclusion A D P x y s' ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y)
    (SSet.yonedaEquiv.symm g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientClosedRoofHomInclusion A D P x y s) :=
  (F.transportTriangle A D P hP x y).homotopy

/-- 得た輸送の境界は、元の指定境界への輸送の商像に全時刻で厳密に一致。 -/
lemma DGActualRoofRelativeFiller.transportHomotopy_boundary
    (hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g) :
    ((∂Δ[n]).ι ▷ Δ[1]) ≫ (F.transportHomotopy A D P hP x y).h =
      F.boundary_transport.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondenceMap A D P x y :=
  (F.transportTriangle A D P hP x y).homotopy_boundary.trans (F.transport_boundary hb)

/-- 得た輸送は、元の指定実分母辺を全時間で厳密に被覆する。 -/
lemma DGActualRoofRelativeFiller.transportHomotopy_projection :
    (F.transportHomotopy A D P hP x y).h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientRoofCorrespondenceProjection A D P x y =
      snd (Δ[n] : SSet.{max u v}) Δ[1] ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominatorEdge A D P x R).edge :=
  (F.transportTriangle A D P hP x y).homotopy_over.trans F.target_over

end SerrePositivity.InfinityCategories.Project.DerivedCategories
