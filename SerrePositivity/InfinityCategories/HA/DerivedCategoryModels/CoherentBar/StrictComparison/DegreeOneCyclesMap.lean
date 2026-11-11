module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.DegreeOneHomologyRepresentative

/-!
概要：閉じた次数一 cochain の実 cycle 上の作用。
方針：標的 cycle の核普遍性へ実次数成分を持ち上げる。
規約：ホモロジー射と同じ代表元を使う。
使われ方：一次ホモロジー射の自然性と線形性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] {K L : Complex R}
  (z : Cochain K L 1) (hz : δ 1 2 z = 0)

def dgDegreeOneCyclesMap (q : ℤ) : K.cycles q ⟶ L.cycles (q + 1) :=
  L.liftCycles (K.iCycles q ≫ z.v q (q + 1) rfl) (q + 2)
    (by apply ComplexShape.next_eq'; change (q + 1) + 1 = q + 2; omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneCochain_cycles_closed R z hz q)

@[reassoc (attr := simp)]
lemma dgDegreeOneCyclesMap_i (q : ℤ) :
    dgDegreeOneCyclesMap R z hz q ≫ L.iCycles (q + 1) = K.iCycles q ≫ z.v q (q + 1) rfl :=
  L.liftCycles_i _ _ _ _

@[reassoc]
lemma dgDegreeOneHomologyMap_cycles (q : ℤ) :
    K.homologyπ q ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap R z hz q =
      dgDegreeOneCyclesMap R z hz q ≫ L.homologyπ (q + 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgDegreeOneHomologyMap_representative R z hz q

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
