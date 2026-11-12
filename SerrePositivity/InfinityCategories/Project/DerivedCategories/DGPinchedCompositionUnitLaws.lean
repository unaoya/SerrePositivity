module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentCompositionRightUnit
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

lemma dgStandardPinched_unit_const {K : SSet.{max u v}} (x : D) (n : ℕ)
    (a : K _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋n⦌)
      ((SSet.const (X := K)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).app _ a)).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x n := by
  let α := (⦋n⦌.const ⦋0⦌ 0).op
  have h := congrArg ULift.down (ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x x).inv.naturality α)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x))))
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := A) (D := D) x x).map α
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x x).inv.app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))).down) at h
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardPinched_unit_vertex A D x] at h
  exact h.trans (ConcreteCategory.congr_hom
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnitMap (R := A) (D := D) x).naturality α) PUnit.unit).symm

lemma dgPinchedCompositionFamilyPrism_first_unit {K : SSet.{max u v}} {x z : D}
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism A D
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) x)))) g =
      snd Δ[1] K ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  let τ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).inv.app _ (g.app _ a.2)).down
  let t := (stdSimplex.objEquiv a.1).toOrderHom
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) x n) τ t =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison (ForgetEnrichment.of (Complex A) x)
        (ForgetEnrichment.of (Complex A) z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToSliceFiber _ _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _).app (Opposite.op ⦋n⦌)) (ULift.up τ) := by
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex _ _ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentCompositionSimplex_first_unit A D]
    rfl
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D z).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) _ τ t) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z).app _ (g.app _ a.2)
  erw [dgStandardPinched_unit_const A D x n a.2]
  rw [hc]
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentHomComparison_slice A D
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z))
      (Opposite.op ⦋n⦌))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).inv.app _ (g.app _ a.2))
  change _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z).app _
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).hom.app _)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).inv.app _) (g.app _ a.2))) at h
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x z).inv_hom_id
      (Opposite.op ⦋n⦌)) (g.app _ a.2)
  exact h.trans (congrArg ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedHomSlice A D x z).app _) he)
/-- 第二入力の閉恒等は、切替後を終点へ送る同じ全 coherent 図式の退化である。 -/
lemma dgPinchedCompositionFamilyPrism_second_unit_val {K : SSet.{max u v}} {x y : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (n : ℕ) (a : (Δ[1] ⊗ K) _⦋n⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism A D f
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D (𝟙 (ForgetEnrichment.of (Complex A) y))))).app
        (Opposite.op ⦋n⦌) a).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
        ((SimplicialThickening.functor
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCompositionUnitCollapse (stdSimplex.objEquiv a.1).toOrderHom).uliftMap).comp SSet
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (C := ClosedCategory A D)
            (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
            (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv.app
              (Opposite.op ⦋n⦌) (f.app _ a.2)).down))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := D) := by
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D y).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) _ _
      (stdSimplex.objEquiv a.1).toOrderHom)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap_val]
  erw [dgStandardPinched_unit_const A D y n a.2]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex (C := ClosedCategory A D)
      (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (D := D) x y).inv.app
        (Opposite.op ⦋n⦌) (f.app _ a.2)).down)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := A) (D := D) y n)
      (stdSimplex.objEquiv a.1).toOrderHom)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := D) = _
  erw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentCompositionSimplex_second_unit A D, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
