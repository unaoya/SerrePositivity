module
public import SerrePositivity.InfinityCategories.Derived.DGInvertingFamilyEvaluation
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyHomotopy

/-!
概要：任意標的への屋根の評価を実 pinched Hom の族として表示し、その実合成を得る。
方針：定値関手の端点を同型で揃え、全パラメータの射の表示を使う。
規約：実合成三角形には標的の quasicategory 性を使う。使われ方：全選択空間の評価比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable {K : SSet.{max u v}} {Y : SSet.{max u v}} (F : dgNerve A D ⟶ Y)
/-- 全パラメータの屋根評価と、その同じ値を表す実 pinched Hom 族。 -/
structure DGInvertingPinchedFamilyEvaluation {q x y : D}
    (d : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (n : K ⟶ DGNerve.pinchedHom A D q y) where
  evaluation : DGInvertingFamilyEvaluation A D F d n
  value : K ⟶ pinchedHom (F.app (Opposite.op ⦋0⦌) (Simplex.vertex x))
    (F.app (Opposite.op ⦋0⦌) (Simplex.vertex y))
  value_eq : intervalFamilyHom (value ≫ pinchedHomToIntervalMappingSpace _ _) =
    (constantFunctorCompIso K (Simplex.vertex x) F).inv ≫ evaluation.value ≫
      (constantFunctorCompIso K (Simplex.vertex y) F).hom
/-- 任意の quasicategory 標的への屋根評価は、実 pinched Hom 族で表示できる。 -/
lemma dgInvertingPinchedFamilyEvaluation_nonempty [Quasicategory Y] (P : Set D)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) {q x y : D}
    (d : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hd : (dgClosedEdge A D d).edge ∈ dgVerdierEdges A D P)
    (n : K ⟶ DGNerve.pinchedHom A D q y) :
    Nonempty (DGInvertingPinchedFamilyEvaluation A D F d n) := by
  obtain ⟨e⟩ := dgInvertingFamilyEvaluation_nonempty A D F P hF d hd n
  obtain ⟨a, ha⟩ := pinchedFamilyHom_surjective K Y _ _
    ((constantFunctorCompIso K (Simplex.vertex x) F).inv ≫ e.value ≫
      (constantFunctorCompIso K (Simplex.vertex y) F).hom)
  exact ⟨⟨e, a, ha⟩⟩
variable [Small.{u} D] [IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {r : K ⟶ dgRoofCorrespondence A D P x y}
variable {s : K ⟶ dgRoofCorrespondence A D P y z}
variable (R : DGFiniteRoofOreData A D P x y z r s)
variable (C : DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 同時細分の三つの実評価族は、同じ関手圏で合成する。 -/
lemma dgInvertingPinchedFamilyEvaluation_comp (hF : InvertsEdges F (dgVerdierEdges A D P))
    (er : DGInvertingPinchedFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingPinchedFamilyEvaluation A D F R.second.denominator.obj.hom
      R.second.coefficient)
    (ec : DGInvertingPinchedFamilyEvaluation A D F
      R.compositeDenominator.obj.hom R.compositeNumerator) :
    intervalFamilyHom (er.value ≫ pinchedHomToIntervalMappingSpace _ _) ≫
      intervalFamilyHom (es.value ≫ pinchedHomToIntervalMappingSpace _ _) =
        intervalFamilyHom (ec.value ≫ pinchedHomToIntervalMappingSpace _ _) := by
  rw [er.value_eq, es.value_eq, ec.value_eq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have h := dgInvertingFamilyEvaluation_comp A D F P x y z R C hF
    er.evaluation es.evaluation ec.evaluation
  simpa only [Category.assoc] using congrArg (fun a =>
    (constantFunctorCompIso K (Simplex.vertex x) F).inv ≫ a ≫
      (constantFunctorCompIso K (Simplex.vertex z) F).hom) h
/-- 三実評価族には、同じパラメータ関手圏内の実合成三角形が存在する。 -/
lemma dgInvertingPinchedFamilyEvaluation_compositionTriangle_nonempty [Quasicategory Y]
    (hF : InvertsEdges F (dgVerdierEdges A D P))
    (er : DGInvertingPinchedFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingPinchedFamilyEvaluation A D F R.second.denominator.obj.hom
      R.second.coefficient)
    (ec : DGInvertingPinchedFamilyEvaluation A D F
      R.compositeDenominator.obj.hom R.compositeNumerator) :
    Nonempty (Truncated.Edge.CompStruct
      (intervalFamilyEdge (er.value ≫ pinchedHomToIntervalMappingSpace _ _))
      (intervalFamilyEdge (es.value ≫ pinchedHomToIntervalMappingSpace _ _))
      (intervalFamilyEdge (ec.value ≫ pinchedHomToIntervalMappingSpace _ _))) := by
  apply compStruct_nonempty_of_homMk_fac
  exact dgInvertingPinchedFamilyEvaluation_comp A D F P x y z R C hF er es ec
end SerrePositivity.InfinityCategories
