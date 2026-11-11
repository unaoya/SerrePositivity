module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseExactProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
/-!
概要：正本比較は完全同値であり、導来 lax pullback は元 dg gluing と同じ安定性を持つ。
方針：構成済みの実同値で安定性を移し、元の二射影の完全性を逆比較と余単位で戻す。
規約：比較の全単体と元の二射影を保持する。二脚の完全性を新しい入力にしない。
使われ方：F2 の安定 lax pullback と半直交分解の比較に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
lemma dgGluingUniverseDerivedNerveLaxComparison_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_isQCatEquivalence R C D M)
lemma dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).inv :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).symm.isQCatEquivalence

variable [Small.{u} D] (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
include hC hD
lemma dgGluingUniverseDerivedLaxPullback_isStable :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M).isStable_iff.mp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerve_isStable R C D M hC hD)

lemma dgGluingUniverseDerivedLaxPullbackFst_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve_isExactFunctor R C D M hC hD
  let := dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  have hi := e.invHomIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
  simp only [e, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_fst, Category.id_comp] at hi
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso hi

lemma dgGluingUniverseDerivedLaxPullbackSnd_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve_isExactFunctor R C D M hC hD
  let := dgGluingUniverseDerivedNerveLaxEquivalence_inv_isExactFunctor R C D M
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence R C D M
  have hi := e.invHomIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u,v,w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M))
  simp only [e, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxEquivalence_hom,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_snd, Category.id_comp] at hi
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_functorIso hi
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
