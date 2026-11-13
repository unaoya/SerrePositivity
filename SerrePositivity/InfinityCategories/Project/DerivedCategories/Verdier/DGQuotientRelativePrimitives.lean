module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGPrimitiveResidual
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGClosedVerdierComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientPrimitiveDenominator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientGradedFractions

/-! # 指定された商の原始元の比較境界付き相対持ち上げ

概要：商で指定された原始元を、元の実分母と原始元および一段高い商内の境界で比較する。
方針：まず元で原始元を作り、指定原始元との差の閉残差を分数表示して閉分子を引く。
規約：入力の原始元を固定し、両微分式を厳密に証明する。使われ方：pinched 境界の相対充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定された商の原始元には、実分母と元の原始元および一段高い実比較境界が存在する。 -/
theorem dgQuotient_exists_relativePrimitive (P : Set D) (hP : localKFlat A D P)
    (x y : D) (k : ℤ) (a : GradedHom A x y (k + 1)) (ha : differential A a = 0)
    (c : GradedHom A ((inclusion A D P).obj x) ((inclusion A D P).obj y) k)
    (hc : differential A c = ((inclusion A D P).map x y).f (k + 1) a) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
      ∃ h : GradedHom A q y k,
        differential A h = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a s ∧
        ∃ b : GradedHom A ((inclusion A D P).obj q) ((inclusion A D P).obj y) (k - 1),
          (homObject A (QuotientObject D P) ((inclusion A D P).obj q)
            ((inclusion A D P).obj y)).d (k - 1) k b =
              _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) (inclusion A D P) k c h s := by
  let F := inclusion A D P
  obtain ⟨q, s, hs, h, hh⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientBoundary_exists_closedPrimitive A D P hP x y k a ha c hc
  let z : GradedHom A (F.obj q) (F.obj y) k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P)
    F k c h s
  have hz : differential A z = 0 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual_closed A D (QuotientObject D P)
    F k a c h s hc hh
  obtain ⟨p, r, hr, e, he, b, hb⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientGraded_exists_fraction A D P hP q y k z hz
  let h' : GradedHom A p y k := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k h r - e
  have hh' : differential A h' = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D (k + 1) a (r ≫ s) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveCorrection_d A D k a h e r s hh he
  have hp : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveResidual A D (QuotientObject D P) F k c h' (r ≫ s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A (QuotientObject D P)
        (q := F.obj p) (x := F.obj q) (y := F.obj y) k z (F.onClosed.map r) -
          (F.map p y).f k e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPrimitiveCorrection_residual A D (QuotientObject D P)
            F k c h e r s
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_image A D (QuotientObject D P) F k z r
  refine ⟨p, r ≫ s, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedVerdierDenominator_comp A D P r s hr hs, h', hh', -b, ?_⟩
  rw [map_neg, hb, hp, hm]
  abel

end SerrePositivity.InfinityCategories.Project.DerivedCategories
