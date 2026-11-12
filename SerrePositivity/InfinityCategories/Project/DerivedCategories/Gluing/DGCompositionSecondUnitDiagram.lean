module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedCompositionUnitLaws
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgGluingCoherentHomSimplex_retract {x y : E} (n : ℕ)
    (a : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := E)).app (Opposite.op ⦋n + 1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := _root_.SerrePositivity.DifferentialGraded.ClosedCategory R E)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
        (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := E) x y).inv.app _ a).down)) = a.val := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardHomToCoherentPinched_comp R E
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y))
        (Opposite.op ⦋n⦌))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := E) x y).inv.app _ a)
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := E) x y).inv_hom_id
      (Opposite.op ⦋n⦌)) a
  exact (congrArg (fun b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) _⦋n⦌ => b.val) h).trans
    (congrArg (fun b : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y) _⦋n⦌ => b.val) he)

lemma dgGluingDGCompositionFamilyPrism_second_unit_diagram
    {K : SSet.{max u v}} {x y : E} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R E x y)
    (n : ℕ) (a : (Δ[1] ⊗ K) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism R E f
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R E (𝟙 (ForgetEnrichment.of (Complex R) y))))).app
        (Opposite.op ⦋n⦌) a).val =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
      SSet.stdSimplex.map (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse (stdSimplex.objEquiv a.1).toOrderHom)) ≫
      SSet.yonedaEquiv.symm (f.app _ a.2).val := by
  rcases a with ⟨t, k⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism_second_unit_val]
  erw [SSet.yonedaEquiv_symm_comp]
  have hn := ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := E)).naturality
      (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory R E)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := E) x y).inv.app _ (f.app _ k)).down))
  erw [hn]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E).map
      (SimplexCategory.mkHom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse (stdSimplex.objEquiv t).toOrderHom)).op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := E)).app (Opposite.op ⦋n + 1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory R E)
          (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y)
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := E) x y).inv.app _ (f.app _ k)).down)))) = _
  rw [dgGluingCoherentHomSimplex_retract]
  rw [← SSet.yonedaEquiv_symm_naturality_left]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
