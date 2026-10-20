module
public import SerrePositivity.InfinityCategories.Derived.DGConstantFamilyInvertible
public import SerrePositivity.InfinityCategories.Derived.DGPinchedFamilyEvaluation

/-!
概要：任意の反転関手の下で、屋根分子族の評価と合成を供給する。
方針：閉分母の定数族の可逆性を使い、評価の構成と分母消去を適用する。
規約：与えられた反転条件だけを使う。使われ方：実 pinched Hom 族への評価の回収。
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
/-- 任意標的への後合成の下での、全パラメータの屋根評価。 -/
abbrev DGInvertingFamilyEvaluation {q x y : D}
    (d : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (n : K ⟶ DGNerve.pinchedHom A D q y) :=
  DGPinchedFamilyEvaluation A D ((hoFunctor.map ((ihom K).map F)).toFunctor) d n
/-- 実分母を反転する関手の下で、屋根分子族の評価が存在する。 -/
lemma dgInvertingFamilyEvaluation_nonempty (P : Set D)
    (hF : InvertsEdges F (dgVerdierEdges A D P)) {q x y : D}
    (d : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (hd : (dgClosedEdge A D d).edge ∈ dgVerdierEdges A D P)
    (n : K ⟶ DGNerve.pinchedHom A D q y) :
    Nonempty (DGInvertingFamilyEvaluation A D F d n) := by
  have := dgInvertingFamilyDenominator_isIso A D P F hF d hd (K := K)
  exact dgPinchedFamilyEvaluation_nonempty A D _ d n
variable [Small.{u} D] [IsDGPretriangulated A D] (P : Set D) (x y z : D)
variable {r : K ⟶ dgRoofCorrespondence A D P x y}
variable {s : K ⟶ dgRoofCorrespondence A D P y z}
variable (R : DGFiniteRoofOreData A D P x y z r s)
variable (C : DGFiniteRoofCompositionPrisms A D P x y z R)
include C
/-- 反転条件だけから、任意標的の三評価族の合成を導く。 -/
lemma dgInvertingFamilyEvaluation_comp (hF : InvertsEdges F (dgVerdierEdges A D P))
    (er : DGInvertingFamilyEvaluation A D F R.first.denominator.obj.hom R.first.coefficient)
    (es : DGInvertingFamilyEvaluation A D F R.second.denominator.obj.hom R.second.coefficient)
    (ec : DGInvertingFamilyEvaluation A D F R.compositeDenominator.obj.hom R.compositeNumerator) :
    er.value ≫ es.value = ec.value := by
  have := dgInvertingFamilyDenominator_isIso A D P F hF
    R.compositeDenominator.obj.hom R.compositeDenominator.property (K := K)
  exact dgPinchedFamilyEvaluation_comp A D _ P x y z R C er es ec
end SerrePositivity.InfinityCategories
