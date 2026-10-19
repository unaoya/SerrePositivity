module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionSlicePrism
public import SerrePositivity.InfinityCategories.Derived.DGVerdierClosedRefinementEdge
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofHomInclusion

/-! # 指定元の閉細分に沿う実商屋根の全係数 prism

概要：元の閉細分の像による前合成と商 Hom の包含を、実商屋根内で全次数で結ぶ。
方針：固定標的の slice prism と元の指定実分母辺を、始域射影の一致で貼る。
規約：全係数単体・全端点を保持する。使われ方：有限相対充填の実全空間への移行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet MonoidalCategory
open CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s t : DGClosedVerdierDenominators A D P x} (r : s ⟶ t)

/-- 指定閉細分に沿う、元の Hom 全体の実屋根内の prism。 -/
def dgQuotientClosedRoofRefinementPrism :
    DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) t.obj.left))
      ((DGQuotient.inclusion A D P).obj y) ⊗ Δ[1] ⟶
      dgQuotientRoofCorrespondence A D P x y :=
  pullback.lift (dgClosedPrecompositionSlicePrism A (DGQuotient.QuotientObject D P)
    ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).onClosed.map r.hom.left))
    (snd _ Δ[1] ≫ SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x r).edge) (by
      have h : SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x r).edge ≫
          dgVerdierOverSource A D P x =
          (SSet.yonedaEquiv (X := dgNerve A D)).symm (dgClosedEdge A D r.hom.left).edge :=
        (SSet.yonedaEquiv_symm_comp _ _).trans
          (congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm
            (dgClosedVerdierDenominatorEdge_source A D P x r))
      have hQ : SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x r).edge ≫
          (dgVerdierOverSource A D P x ≫ dgQuotientNerveProjection A D P) =
          (SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
            (dgClosedEdge A (DGQuotient.QuotientObject D P)
              ((DGQuotient.inclusion A D P).onClosed.map r.hom.left)).edge := by
        have hm := (SSet.yonedaEquiv_symm_comp (dgClosedEdge A D r.hom.left).edge
          (dgQuotientNerveProjection A D P)).trans
            (congrArg (SSet.yonedaEquiv (X := dgQuotientNerve A D P)).symm
              (dgClosedEdge_map A D (DGQuotient.inclusion A D P) r.hom.left))
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ dgQuotientNerveProjection A D P) h).trans hm)
      exact (dgClosedPrecompositionSlicePrism_source A (DGQuotient.QuotientObject D P)
        ((DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map r.hom.left)).trans
          ((congrArg (fun f => snd _ Δ[1] ≫ f) hQ).symm.trans (Category.assoc _ _ _).symm))


/-- 全係数の実屋根 prism の分子成分は、元の指定閉前合成の slice prism。 -/
lemma dgQuotientClosedRoofRefinementPrism_target :
    dgQuotientClosedRoofRefinementPrism A D P x y r ≫ dgQuotientRoofCorrespondenceTarget A D P x y =
      dgClosedPrecompositionSlicePrism A (DGQuotient.QuotientObject D P)
    ((DGQuotient.inclusion A D P).obj y) ((DGQuotient.inclusion A D P).onClosed.map r.hom.left) :=
  pullback.lift_fst _ _ _

/-- 全係数の実屋根 prism は、元の指定実分母辺に沿う。 -/
lemma dgQuotientClosedRoofRefinementPrism_projection :
    dgQuotientClosedRoofRefinementPrism A D P x y r ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      snd _ Δ[1] ≫ SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x r).edge :=
  pullback.lift_snd _ _ _

/-- 実屋根 prism の零端点は、指定閉細分による全係数の前合成の包含。 -/
lemma dgQuotientClosedRoofRefinementPrism_zero :
    SSet.ι₀ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r =
      pinchedClosedPrecomposition A (DGQuotient.QuotientObject D P)
        (y := (DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map r.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s := by
  apply pullback.hom_ext
  · change (SSet.ι₀ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
      dgQuotientRoofCorrespondenceTarget A D P x y =
      (pinchedClosedPrecomposition A (DGQuotient.QuotientObject D P)
        (y := (DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map r.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s) ≫ dgQuotientRoofCorrespondenceTarget A D P x y
    simp only [Category.assoc, dgQuotientClosedRoofRefinementPrism_target,
      dgClosedPrecompositionSlicePrism_zero, dgQuotientClosedRoofHomInclusion_target]
    rfl
  · change (SSet.ι₀ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      (pinchedClosedPrecomposition A (DGQuotient.QuotientObject D P)
        (y := (DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map r.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s) ≫
        dgQuotientRoofCorrespondenceProjection A D P x y
    simp only [Category.assoc, dgQuotientClosedRoofRefinementPrism_projection,
      roofEdgeCylinder_zero, dgQuotientClosedRoofHomInclusion_projection, SSet.comp_const]

/-- 実屋根 prism の一端点は、元の全係数の包含。 -/
lemma dgQuotientClosedRoofRefinementPrism_one :
    SSet.ι₁ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r =
      dgQuotientClosedRoofHomInclusion A D P x y t := by
  apply pullback.hom_ext
  · change (SSet.ι₁ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
      dgQuotientRoofCorrespondenceTarget A D P x y =
      dgQuotientClosedRoofHomInclusion A D P x y t ≫
        dgQuotientRoofCorrespondenceTarget A D P x y
    simp only [Category.assoc, dgQuotientClosedRoofRefinementPrism_target,
      dgClosedPrecompositionSlicePrism_one, dgQuotientClosedRoofHomInclusion_target]
    exact Eq.refl _
  · change (SSet.ι₁ ≫ dgQuotientClosedRoofRefinementPrism A D P x y r) ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      dgQuotientClosedRoofHomInclusion A D P x y t ≫
        dgQuotientRoofCorrespondenceProjection A D P x y
    simp only [Category.assoc, dgQuotientClosedRoofRefinementPrism_projection,
      roofEdgeCylinder_one, dgQuotientClosedRoofHomInclusion_projection]

/-- 指定閉細分による全次数の前合成は、実屋根内で元の係数包含とホモトピック。 -/
def dgQuotientClosedRoofRefinementHomotopy :
    SSet.Homotopy (pinchedClosedPrecomposition A (DGQuotient.QuotientObject D P)
        (y := (DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map r.hom.left) ≫
      dgQuotientClosedRoofHomInclusion A D P x y s)
      (dgQuotientClosedRoofHomInclusion A D P x y t) where
  h := dgQuotientClosedRoofRefinementPrism A D P x y r
  h₀ := dgQuotientClosedRoofRefinementPrism_zero A D P x y r
  h₁ := dgQuotientClosedRoofRefinementPrism_one A D P x y r
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.2

end SerrePositivity.InfinityCategories
