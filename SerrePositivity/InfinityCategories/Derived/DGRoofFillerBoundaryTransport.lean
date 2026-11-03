module
public import SerrePositivity.InfinityCategories.Derived.DGClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Derived.DGQuotientClosedRoofRefinementPrism
public import SerrePositivity.InfinityCategories.Core.HomotopyPrecomposition

/-! # 細分後の実充填境界と元の指定境界の比較

概要：細分後で厳密に充填した境界を、元の分母上の指定境界へ実ホモトピーで結ぶ。
方針：全係数 prism を指定境界で引き戻し、始端だけを厳密な充填等式で照合する。
規約：元の分母上で境界が厳密に等しいとは主張しない。使われ方：有限充填の幾何的界面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) (x y : D) {s' s : DGClosedVerdierDenominators A D P x} (R : s' ⟶ s)

/-- 細分後の係数の厳密な充填境界は、実屋根への包含後も厳密に一致する。 -/
lemma dgClosedRoofFiller_boundary {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s' =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left ≫
        dgClosedRoofHomInclusion A D P x y s' :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ dgClosedRoofHomInclusion A D P x y s') ht).trans
      (Category.assoc _ _ _))

/-- 実充填の境界と元の指定境界を、元の指定分母辺に沿って結ぶ。 -/
def dgClosedRoofFillerBoundaryHomotopy {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    SSet.Homotopy
      ((∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t ≫ dgClosedRoofHomInclusion A D P x y s')
      (b ≫ dgClosedRoofHomInclusion A D P x y s) := by
  let H := stableHomotopyPrecomp b (dgClosedRoofRefinementHomotopy A D P x y R)
  exact {
    h := H.h
    h₀ := H.h₀.trans (dgClosedRoofFiller_boundary A D P x y R b t ht).symm
    h₁ := H.h₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.2 }

/-- 充填境界の比較の台は、境界の全係数で引き戻した指定実屋根 prism。 -/
lemma dgClosedRoofFillerBoundaryHomotopy_h {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    (dgClosedRoofFillerBoundaryHomotopy A D P x y R b t ht).h =
      (b ▷ Δ[1]) ≫ dgClosedRoofRefinementPrism A D P x y R := rfl

/-- 指定商単体を細分後の実分母から元の実分母へ戻す実ホモトピー。 -/
def dgQuotientRoofSimplexRefinementHomotopy {n : ℕ}
    (g : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((DGQuotient.inclusion A D P).obj y)) _⦋n⦌) :
    SSet.Homotopy
      (SSet.yonedaEquiv.symm g ≫ pinchedClosedPrecomposition A (DGQuotient.QuotientObject D P)
        (y := (DGQuotient.inclusion A D P).obj y)
        ((DGQuotient.inclusion A D P).onClosed.map R.hom.left) ≫
        dgQuotientClosedRoofHomInclusion A D P x y s')
      (SSet.yonedaEquiv.symm g ≫ dgQuotientClosedRoofHomInclusion A D P x y s) :=
  stableHomotopyPrecomp (SSet.yonedaEquiv.symm g)
    (dgQuotientClosedRoofRefinementHomotopy A D P x y R)

/-- 実充填境界の輸送は、元の指定実分母辺を厳密に被覆する。 -/
lemma dgClosedRoofFillerBoundaryHomotopy_projection {n : ℕ}
    (b : (∂Δ[n] : SSet.{max u v}) ⟶
      DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s.obj.left) y)
    (t : (DGNerve.pinchedHom A D (ForgetEnrichment.to (Complex A) s'.obj.left) y) _⦋n⦌)
    (ht : (∂Δ[n]).ι ≫ SSet.yonedaEquiv.symm t =
      b ≫ pinchedClosedPrecomposition A D (y := y) R.hom.left) :
    (dgClosedRoofFillerBoundaryHomotopy A D P x y R b t ht).h ≫
      dgRoofCorrespondenceProjection A D P x y =
      snd (∂Δ[n] : SSet.{max u v}) Δ[1] ≫
        SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x R).edge := by
  rw [dgClosedRoofFillerBoundaryHomotopy_h, Category.assoc,
    dgClosedRoofRefinementPrism_projection, ← Category.assoc, whiskerRight_snd]

/-- 指定商単体の輸送も、同じ元の指定実分母辺を厳密に被覆する。 -/
lemma dgQuotientRoofSimplexRefinementHomotopy_projection {n : ℕ}
    (g : (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P)
      ((DGQuotient.inclusion A D P).obj (ForgetEnrichment.to (Complex A) s.obj.left))
      ((DGQuotient.inclusion A D P).obj y)) _⦋n⦌) :
    (dgQuotientRoofSimplexRefinementHomotopy A D P x y R g).h ≫
      dgQuotientRoofCorrespondenceProjection A D P x y =
      snd (Δ[n] : SSet.{max u v}) Δ[1] ≫
        SSet.yonedaEquiv.symm (dgClosedVerdierDenominatorEdge A D P x R).edge := by
  change ((SSet.yonedaEquiv.symm g ▷ Δ[1]) ≫
    dgQuotientClosedRoofRefinementPrism A D P x y R) ≫ _ = _
  rw [Category.assoc, dgQuotientClosedRoofRefinementPrism_projection,
    ← Category.assoc, whiskerRight_snd]

end SerrePositivity.InfinityCategories
