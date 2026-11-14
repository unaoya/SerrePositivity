module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGInvertingFamilyEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyHomotopy

/-!
概要：任意標的への屋根の評価を実 pinched Hom の族として表示し、その実合成を得る。
方針：定値関手の端点を同型で揃え、全パラメータの射の表示を使う。
規約：実合成三角形には標的の quasicategory 性を使う。使われ方：全選択空間の評価比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {K : SSet.{max u v}} {Y : SSet.{max u v}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ Y)
/-- 全パラメータの屋根評価と、その同じ値を表す実 pinched Hom 族。 -/
structure DGInvertingPinchedFamilyEvaluation {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) where
  evaluation : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInvertingFamilyEvaluation A D F d n
  value : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
  value_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) F).inv ≫ evaluation.value ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) F).hom
/-- 任意の quasicategory 標的への屋根評価は、実 pinched Hom 族で表示できる。 -/
lemma dgInvertingPinchedFamilyEvaluation_nonempty [Quasicategory Y] (P : Set D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) :
    Nonempty (DGInvertingPinchedFamilyEvaluation A D F d n) := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFamilyEvaluation_nonempty A D F P hF d hd n
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_surjective K Y _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) F).inv ≫ e.value ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) F).hom)
  exact ⟨⟨e, a, ha⟩⟩
variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData A D P x y z r s)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 同時細分の三つの実評価族は、同じ関手圏で合成する。 -/
lemma dgInvertingPinchedFamilyEvaluation_comp (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (er : DGInvertingPinchedFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingPinchedFamilyEvaluation A D F R.second.denominator.obj.hom
      R.second.coefficient)
    (ec : DGInvertingPinchedFamilyEvaluation A D F
      R.compositeDenominator.obj.hom R.compositeNumerator) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (er.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (es.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (ec.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  rw [er.value_eq, es.value_eq, ec.value_eq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFamilyEvaluation_comp A D F P x y z R C hF
    er.evaluation es.evaluation ec.evaluation
  simpa only [Category.assoc] using congrArg (fun a =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) F).inv ≫ a ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) F).hom) h
/-- 三実評価族には、同じパラメータ関手圏内の実合成三角形が存在する。 -/
lemma dgInvertingPinchedFamilyEvaluation_compositionTriangle_nonempty [Quasicategory Y]
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (er : DGInvertingPinchedFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingPinchedFamilyEvaluation A D F R.second.denominator.obj.hom
      R.second.coefficient)
    (ec : DGInvertingPinchedFamilyEvaluation A D F
      R.compositeDenominator.obj.hom R.compositeNumerator) :
    Nonempty (Truncated.Edge.CompStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (er.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (es.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyEdge (ec.value ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  exact dgInvertingPinchedFamilyEvaluation_comp A D F P x y z R C hF er es ec
end SerrePositivity.InfinityCategories.Project.DerivedCategories
