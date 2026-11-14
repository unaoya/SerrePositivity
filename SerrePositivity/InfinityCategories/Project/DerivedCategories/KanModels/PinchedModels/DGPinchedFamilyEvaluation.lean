module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGFiniteRoofFunctorRelations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.RoofEvaluationComposition

/-!
概要：全パラメータの屋根分子族の評価方程式と合成を構成する。
方針：実四三角形族を同じ関手圏の四関係へ移し、合成分母を消去する。
規約：任意の圏への関手を扱う。使われ方：任意の反転関手による評価族の合成。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {K : SSet.{max u v}} {E : Type w} [Category.{t} E]
variable (G : hoFunctor.obj ((ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) ⥤ E)
/-- 全パラメータの屋根分子族の値と、指定分母を掛け戻す評価方程式。 -/
structure DGPinchedFamilyEvaluation {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) where
  value : G.obj (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
    (A := A) x)))) ⟶
    G.obj (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A :=
      A) y))))
  fac : G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d))) ≫ value =
    G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D n)
/-- 分母の像が可逆なら、同じ分子族の評価が存在する。 -/
lemma dgPinchedFamilyEvaluation_nonempty {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y)
    [IsIso (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d))))] :
    Nonempty (DGPinchedFamilyEvaluation A D G d n) := by
  refine ⟨⟨inv (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D
    (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D d)))) ≫ G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D n), ?_⟩⟩
  simp only [IsIso.hom_inv_id_assoc]
variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData A D P x y z r s)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 実四三角形族と三評価式から、任意の圏における評価の合成を得る。 -/
lemma dgPinchedFamilyEvaluation_comp
    (er : DGPinchedFamilyEvaluation A D G R.first.denominator.obj.hom R.first.coefficient)
    (es : DGPinchedFamilyEvaluation A D G R.second.denominator.obj.hom R.second.coefficient)
    (ec : DGPinchedFamilyEvaluation A D G R.compositeDenominator.obj.hom R.compositeNumerator)
    [Epi (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (X := K)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.compositeDenominator.obj.hom))))] :
    er.value ≫ es.value = ec.value := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofEvaluation_comp
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D
      R.ore.combinedDenominator))))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D
      R.first.denominator.obj.hom))))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.first.coefficient))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D
      R.second.denominator.obj.hom))))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.second.coefficient))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.ore.lift))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D
      R.compositeDenominator.obj.hom))))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D R.compositeNumerator))
    (G.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A D (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomCompositionFamily
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A D R.ore.combinedDenominator)) R.first.coefficient)))
    _ _ _ _ er.value es.value ec.value er.fac es.fac ec.fac
  · rw [← G.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofFunctor_denominator A D P x y z R C]
  · rw [← G.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofFunctor_first A D P x y z R C]
  · rw [← G.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofFunctor_second A D P x y z R C]
  · rw [← G.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteRoofFunctor_numerator A D P x y z R C]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
