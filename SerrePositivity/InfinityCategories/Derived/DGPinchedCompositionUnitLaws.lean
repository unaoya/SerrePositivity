module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCompositionRightUnit
/-!
概要：元の coherent 合成 prism の閉恒等入力を全パラメーターで退化表示する。
方針：閉恒等頂点を標準単位へ戻し、coherent 図式全体の単位則を同じ target slice へ移す。
規約：Small 仮定なし。元の構成と全端点を保持する。
使われ方：D2 が augmentation の二面の標準合成三角形を退化として回収する入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma dgStandardPinched_unit_const {K : SSet.{max u v}} (x : D) (n : ℕ)
    (a : K _⦋n⦌) :
    ((standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋n⦌)
      ((SSet.const (X := K)
        (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).app _ a)).down =
      standardUnit (R := A) (D := D) x n := by
  let α := (⦋n⦌.const ⦋0⦌ 0).op
  have h := congrArg ULift.down (ConcreteCategory.congr_hom
    ((standardHomPinchedIso (R := A) (D := D) x x).inv.naturality α)
      (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))))
  change _ = (standardHomSpace (R := A) (D := D) x x).map α
    (((standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋0⦌)
      (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).down) at h
  erw [dgStandardPinched_unit_vertex A D x] at h
  exact h.trans (ConcreteCategory.congr_hom
    ((standardUnitMap (R := A) (D := D) x).naturality α) PUnit.unit).symm

lemma dgPinchedCompositionFamilyPrism_first_unit {K : SSet.{max u v}} {x z : D}
    (g : K ⟶ DGNerve.pinchedHom A D x z) :
    dgPinchedCompositionFamilyPrism A D
      (SSet.const (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))) g =
      snd Δ[1] K ≫ g ≫ dgPinchedHomSlice A D x z := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  let τ := ((standardHomPinchedIso (R := A) (D := D) x z).inv.app _ (g.app _ a.2)).down
  let t := (stdSimplex.objEquiv a.1).toOrderHom
  have hc : coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) x)
      (Z := ForgetEnrichment.of (Complex A) z)
      (standardUnit (R := A) (D := D) x n) τ t =
      ((coherentHomComparison (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) z) ≫ pinchedHomToSliceFiber _ _ ≫
        vertexFiberι _ _).app (Opposite.op ⦋n⦌)) (ULift.up τ) := by
    apply Subtype.ext
    change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (coherentCompositionSimplex _ _ _) = _
    rw [dgCoherentCompositionSimplex_first_unit A D]
    rfl
  change (dgCoherentTargetSliceMap A D z).app _
    (coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) x)
      (Z := ForgetEnrichment.of (Complex A) z) _ τ t) =
    (dgPinchedHomSlice A D x z).app _ (g.app _ a.2)
  erw [dgStandardPinched_unit_const A D x n a.2]
  rw [hc]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgCoherentHomComparison_slice A D
      (ForgetEnrichment.of (Complex A) x) (ForgetEnrichment.of (Complex A) z))
      (Opposite.op ⦋n⦌))
    ((standardHomPinchedIso (R := A) (D := D) x z).inv.app _ (g.app _ a.2))
  change _ = (dgPinchedHomSlice A D x z).app _
    (((standardHomPinchedIso (R := A) (D := D) x z).hom.app _)
      (((standardHomPinchedIso (R := A) (D := D) x z).inv.app _) (g.app _ a.2))) at h
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (standardHomPinchedIso (R := A) (D := D) x z).inv_hom_id
      (Opposite.op ⦋n⦌)) (g.app _ a.2)
  exact h.trans (congrArg ((dgPinchedHomSlice A D x z).app _) he)
/-- 第二入力の閉恒等は、切替後を終点へ送る同じ全 coherent 図式の退化である。 -/
lemma dgPinchedCompositionFamilyPrism_second_unit_val {K : SSet.{max u v}} {x y : D}
    (f : K ⟶ DGNerve.pinchedHom A D x y) (n : ℕ) (a : (Δ[1] ⊗ K) _⦋n⦌) :
    ((dgPinchedCompositionFamilyPrism A D f
      (SSet.const (pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) y))))).app
        (Opposite.op ⦋n⦌) a).val =
      (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        ((SimplicialThickening.functor
          (dgCompositionUnitCollapse (stdSimplex.objEquiv a.1).toOrderHom).uliftMap).comp SSet
          (coherentHomComparisonSimplex (C := ClosedCategory A D)
            (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
            (((standardHomPinchedIso (R := A) (D := D) x y).inv.app
              (Opposite.op ⦋n⦌) (f.app _ a.2)).down))) ≫
        coherentComparison (R := A) (D := D) := by
  change ((dgCoherentTargetSliceMap A D y).app _
    (coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      (Z := ForgetEnrichment.of (Complex A) y) _ _
      (stdSimplex.objEquiv a.1).toOrderHom)).val = _
  rw [dgCoherentTargetSliceMap_val]
  erw [dgStandardPinched_unit_const A D y n a.2]
  change ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (Complex A) x) (Y := ForgetEnrichment.of (Complex A) y)
      (Z := ForgetEnrichment.of (Complex A) y)
      (((standardHomPinchedIso (R := A) (D := D) x y).inv.app
        (Opposite.op ⦋n⦌) (f.app _ a.2)).down)
      (standardUnit (R := A) (D := D) y n)
      (stdSimplex.objEquiv a.1).toOrderHom)) ≫ coherentComparison (R := A) (D := D) = _
  erw [← dgCoherentCompositionSimplex_second_unit A D, Category.assoc]

end SerrePositivity.InfinityCategories
