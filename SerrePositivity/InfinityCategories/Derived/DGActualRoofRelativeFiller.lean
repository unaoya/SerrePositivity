module
public import SerrePositivity.InfinityCategories.Derived.DGRoofFillerTransportCompatibility
public import SerrePositivity.InfinityCategories.Derived.DGRoofFillerBoundaryTransport
public import SerrePositivity.InfinityCategories.Derived.DGRoofBoundaryHomotopy

/-! # 実屋根の相対充填と指定分母への輸送のデータ

概要：係数の厳密な境界、元の境界への輸送、商目標への比較を一つの実データに保持する。
方針：二つの輸送は元の実分母辺を被覆し、相対比較は細分後の分母に定値と要求する。
規約：二輸送の境界整合性を保持し、二重 prism 全体の充填は別に証明する。
使われ方：有限充填の受入界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 共通細分後の実充填、元の境界・商目標への輸送、境界固定比較と全分母射影。 -/
structure DGActualRoofRelativeFiller (P : Set D) (x y : D)
    {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s) {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (g : (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((inclusion A D P).obj y)) _⦋n⦌)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌) where
  /-- 細分後の係数上の境界は厳密に指定境界の前合成。 -/
  coefficient_boundary : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
    b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left
  /-- 実充填の境界は、元の分母上の指定境界に実ホモトピーで結ばれる。 -/
  boundary_transport : SSet.Homotopy
    ((∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s')
    (b ≫ dgClosedRoofHomInclusion A D P x y s)
  /-- 境界の輸送は元の指定実分母辺に沿う。 -/
  boundary_over : boundary_transport.h ≫ dgRoofCorrespondenceProjection A D P x y =
    snd (∂Δ[n] : SSet.{max u v}) Δ[1] ≫
      SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x R).edge
  /-- 細分後の指定商目標は、元の分母上の元の指定目標に結ばれる。 -/
  target_transport : SSet.Homotopy
    (SSet.yonedaEquiv.symm g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s')
    (SSet.yonedaEquiv.symm g ≫ dgQuotientClosedRoofHomInclusion A D P x y s)
  /-- 商目標の輸送も同じ元の指定実分母辺に沿う。 -/
  target_over : target_transport.h ≫ dgQuotientRoofCorrespondenceProjection A D P x y =
    snd (Δ[n] : SSet.{max u v}) Δ[1] ≫
      SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x R).edge
  /-- 入力境界が商単体の境界なら、二輸送はその全境界・全時刻で一致する。 -/
  transport_boundary :
    b ≫ pinchedHomChainMap ((inclusion A D P).map
      (ForgetEnrichment.to (Complex A) s.obj.left) y) =
        (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm g →
      ((∂Δ[n]).ι ▷ (Δ[1] : SSet.{max u v})) ≫ target_transport.h =
        boundary_transport.h ≫ dgRoofCorrespondenceMap A D P x y
  /-- 細分後の商目標と実充填の商像を、全境界上で厳密に定値の比較で結ぶ。 -/
  comparison : RoofBoundaryFixedHomotopy
    (SSet.yonedaEquiv.symm g ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map R.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s')
    (SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s' ≫
      dgRoofCorrespondenceMap A D P x y)
  /-- 相対比較は全時間で同じ細分後の実分母に厳密に定値。 -/
  comparison_over : comparison.homotopy.h ≫ dgQuotientRoofCorrespondenceProjection A D P x y =
    SSet.const (dgClosedVerdierDenominatorVertex A D P x s')

/-- 細分後の実充填の境界は、細分した指定境界と厳密に一致する。 -/
lemma DGActualRoofRelativeFiller.actual_boundary {P : Set D} {x y : D}
    {s' s : DGClosedVerdierDenominators A D P x} {R : s' ⟶ s} {n : ℕ}
    {b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y}
    {g : (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((inclusion A D P).obj y)) _⦋n⦌}
    {t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌}
    (F : DGActualRoofRelativeFiller A D P x y R b g t) :
    (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s' =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left ≫
        dgClosedRoofHomInclusion A D P x y s' :=
  dgClosedRoofFiller_boundary A D P x y R b t F.coefficient_boundary

end SerrePositivity.InfinityCategories
