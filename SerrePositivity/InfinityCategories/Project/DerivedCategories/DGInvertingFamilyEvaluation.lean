module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGConstantFamilyInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedFamilyEvaluation

/-!
概要：任意の反転関手の下で、屋根分子族の評価と合成を供給する。
方針：閉分母の定数族の可逆性を使い、評価の構成と分母消去を適用する。
規約：与えられた反転条件だけを使う。使われ方：実 pinched Hom 族への評価の回収。
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
/-- 任意標的への後合成の下での、全パラメータの屋根評価。 -/
abbrev DGInvertingFamilyEvaluation {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPinchedFamilyEvaluation A D ((hoFunctor.map ((ihom K).map F)).toFunctor) d n
/-- 実分母を反転する関手の下で、屋根分子族の評価が存在する。 -/
lemma dgInvertingFamilyEvaluation_nonempty (P : Set D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)) {q x y : D}
    (d : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (hd : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D d).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P)
    (n : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D q y) :
    Nonempty (DGInvertingFamilyEvaluation A D F d n) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFamilyDenominator_isIso A D P F hF d hd (K := K)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyEvaluation_nonempty A D _ d n
variable [Small.{u} D] [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {r : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P x y}
variable {s : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRoofCorrespondence A D P y z}
variable (R : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofOreData A D P x y z r s)
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 反転条件だけから、任意標的の三評価族の合成を導く。 -/
lemma dgInvertingFamilyEvaluation_comp (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P))
    (er : DGInvertingFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingFamilyEvaluation A D F R.second.denominator.obj.hom R.second.coefficient)
    (ec : DGInvertingFamilyEvaluation A D F R.compositeDenominator.obj.hom R.compositeNumerator) :
    er.value ≫ es.value = ec.value := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgInvertingFamilyDenominator_isIso A D P F hF
    R.compositeDenominator.obj.hom R.compositeDenominator.property (K := K)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyEvaluation_comp A D _ P x y z R C er es ec
end SerrePositivity.InfinityCategories.Project.DerivedCategories
