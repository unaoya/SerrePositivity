module
public import SerrePositivity.InfinityCategories.Derived.DGPinchedCompositionUnitLaws
/-!
概要：第二閉恒等入力の coherent 縮約表示を元の dg nerve の単体へ戻す。
方針：標準 Hom 比較の厳密な片側逆と比較射の自然性を用いる。
規約：Small 仮定なしで全次数・全パラメーターを保持する。
使われ方：同じ標準合成三角形の σ₁ 退化を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

lemma dgGluingCoherentHomSimplex_retract {x y : E} (n : ℕ)
    (a : (DGNerve.pinchedHom R E x y) _⦋n⦌) :
    (coherentComparison (R := R) (D := E)).app (Opposite.op ⦋n + 1⦌)
      (coherentHomComparisonSimplex (C := ClosedCategory R E)
        (X := ForgetEnrichment.of (Complex R) x) (Y := ForgetEnrichment.of (Complex R) y)
        (((standardHomPinchedIso (R := R) (D := E) x y).inv.app _ a).down)) = a.val := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (dgStandardHomToCoherentPinched_comp R E
      (ForgetEnrichment.of (Complex R) x) (ForgetEnrichment.of (Complex R) y))
        (Opposite.op ⦋n⦌))
    ((standardHomPinchedIso (R := R) (D := E) x y).inv.app _ a)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (standardHomPinchedIso (R := R) (D := E) x y).inv_hom_id
      (Opposite.op ⦋n⦌)) a
  exact (congrArg (fun b : (DGNerve.pinchedHom R E x y) _⦋n⦌ => b.val) h).trans
    (congrArg (fun b : (DGNerve.pinchedHom R E x y) _⦋n⦌ => b.val) he)

lemma dgGluingDGCompositionFamilyPrism_second_unit_diagram
    {K : SSet.{max u v}} {x y : E} (f : K ⟶ DGNerve.pinchedHom R E x y)
    (n : ℕ) (a : (Δ[1] ⊗ K) _⦋n⦌) :
    ((dgPinchedCompositionFamilyPrism R E f
      (SSet.const (pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y))))).app
        (Opposite.op ⦋n⦌) a).val =
    (joinStdSimplexIso n 0).hom ≫
      SSet.stdSimplex.map (SimplexCategory.mkHom
        (dgCompositionUnitCollapse (stdSimplex.objEquiv a.1).toOrderHom)) ≫
      SSet.yonedaEquiv.symm (f.app _ a.2).val := by
  rcases a with ⟨t, k⟩
  rw [dgPinchedCompositionFamilyPrism_second_unit_val]
  erw [SSet.yonedaEquiv_symm_comp]
  have hn := ConcreteCategory.congr_hom
    ((coherentComparison (R := R) (D := E)).naturality
      (SimplexCategory.mkHom
        (dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op)
    (coherentHomComparisonSimplex (C := ClosedCategory R E)
      (X := ForgetEnrichment.of (Complex R) x) (Y := ForgetEnrichment.of (Complex R) y)
      (((standardHomPinchedIso (R := R) (D := E) x y).inv.app _ (f.app _ k)).down))
  erw [hn]
  change (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    ((dgNerve R E).map
      (SimplexCategory.mkHom
        (dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op
      ((coherentComparison (R := R) (D := E)).app (Opposite.op ⦋n + 1⦌)
        (coherentHomComparisonSimplex (C := ClosedCategory R E)
          (X := ForgetEnrichment.of (Complex R) x) (Y := ForgetEnrichment.of (Complex R) y)
          (((standardHomPinchedIso (R := R) (D := E) x y).inv.app _ (f.app _ k)).down)))) = _
  rw [dgGluingCoherentHomSimplex_retract]
  rw [← SSet.yonedaEquiv_symm_naturality_left]
end SerrePositivity.InfinityCategories
