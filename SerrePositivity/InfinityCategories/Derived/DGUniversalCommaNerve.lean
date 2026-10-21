module
public import SerrePositivity.InfinityCategories.Derived.DGUniversalCommaTarget
public import SerrePositivity.InfinityCategories.Derived.DGFunctorTrivialFibration
/-!
概要：普遍余単位の実 comma の標的 nerve 射影の厳密切断から、全単体上の逆作用を作る。
方針：実対象と全 Hom の各次数全射準同型性から自明 Kan fibration を得る。
規約：まだ ∞ 随伴の三角式は主張しない。使われ方：一般 RHom の coherent な実関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C E : Type (max (u + 1) v))
  [DGCategory R C] [DGCategory R E] (F : DGFunctor R C E)
  (h : ∀ y : E, Nonempty (DGUniversalCounit R C E F y))
include h
/-- 同じ実 comma の標的 nerve 射影は自明 Kan fibration。 -/
lemma dgUniversalCommaTargetNerve_trivialKanFibration :
    TrivialKanFibration (dgNerve.map (dgUniversalCommaTarget R C E F)) :=
  dgNerve_map_trivialKanFibration_of_surjective_quasiIso
    (dgUniversalCommaTarget R C E F) (dgUniversalCommaTarget_obj_surjective R C E F h)
    (dgUniversalCommaTarget_degree_surjective R C E F)
    (dgUniversalCommaTarget_map_quasiIso R C E F)
/-- 同じ標的射影とその厳密切断を持つ実 ∞ 圏同値。 -/
def dgUniversalCommaNerveEquivalence :
    QCatEquivalence (dgNerve R (DGUniversalComma R C E F)) (dgNerve R E) := by
  let := dgUniversalCommaTargetNerve_trivialKanFibration R C E F h
  exact qCatEquivalenceOfTrivialKanFibration (dgNerve.map (dgUniversalCommaTarget R C E F))
/-- 同じ実逆写像は、元の標的射影の全単体上の厳密切断。 -/
lemma dgUniversalCommaNerveEquivalence_inv_hom :
    (dgUniversalCommaNerveEquivalence R C E F h).inv ≫
      dgNerve.map (dgUniversalCommaTarget R C E F) = 𝟙 _ := by
  let := dgUniversalCommaTargetNerve_trivialKanFibration R C E F h
  exact Classical.choose_spec (trivialKanFibration_exists_section
    (dgNerve.map (dgUniversalCommaTarget R C E F)))
/-- 普遍余単位の厳密切断と実始域射影から得る、全単体上の右随伴候補。 -/
def dgUniversalRightAdjointCandidate : dgNerve R E ⟶ dgNerve R C :=
  (dgUniversalCommaNerveEquivalence R C E F h).inv ≫
    dgNerve.map (dgUniversalCommaSource R C E F)
end SerrePositivity.InfinityCategories
