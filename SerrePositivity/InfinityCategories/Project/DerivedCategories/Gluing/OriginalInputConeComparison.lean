module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetNativeConeComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.OriginalInputLaxEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.LaxCospanIsoCofiberComparison
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeZero
/-! 元二脚の指定全 lax 比較と固定 corner 評価を持つ、元実 cone の全比較入力。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits SSet DifferentialGraded KST.SConstruction
open _root_.SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R A B L
local notation "DR" => DGSmallPerfectArrowTarget R A C G
local notation "V" => DGOdotCorner R d
local notation "P" => dgSmallPerfectSquareLeftMap R A B C E L G p q
local notation "Q" => dgSmallPerfectSquareRightMap R A B C E L G p q
local instance dgGluingOriginalInputConeBase_pretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R V :=
  dgOdotMilnorCorner_pretriangulated R d
local instance dgGluingOriginalInputConeBase_stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R V) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R V
attribute [local irreducible] dgHomGluingBimodule

def dgGluingOriginalInputConeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorNativeLaxComparison R d).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d).gluing.hom ≫
        (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotTargetFunctor R d) ≫ (dgOdotMilnorCornerEvaluation R d).hom) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNativeDerivedLaxEquivalence.{u, 0} R CL DR V P Q
  let n := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNerveLaxComparison.{u, 0} R CL DR V P Q
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalInputLaxCospanEquivalence R d
  let c := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).hom
  let v := (dgOdotMilnorCornerEvaluation R d).hom
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYoneda R V)
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgHomGluingConeFunctor R CL DR V P Q)
  let δ₀ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R V)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q))
  let δ₁ := (exactLaxDifference (dgOdotLowerExactMap R d) (dgOdotUpperExactMap R d)).hom
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((dgOdotMilnorNativeLaxComparison R d).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d).gluing.hom ≫ δ₁))
      (n ≫ t.hom ≫ δ₁) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (e.hom ≫ (((e.inv ≫ n) ≫ t.hom) ≫ δ₁)) _
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, Category.id_comp] using
      e.homInvIso.postcomp (n ≫ t.hom ≫ δ₁)
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (n ≫ t.hom ≫ δ₁) (n ≫ δ₀ ≫ c) := by
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.laxCospanIsoCofiberComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)
      (dgOdotLowerExactMap R d).hom (dgOdotUpperExactMap R d).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).hom c
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftLeg R d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightLeg R d)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxLeftEquivalence R d).isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxRightEquivalence R d).isQCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxCornerEquivalence R d).isQCatEquivalence).precomp n
  let z : V := dgSmallPerfectEnvelopeZero R _ _ _
  have hz : IsZero (ForgetEnrichment.of (Complex R) z) :=
    dgSmallPerfectEnvelopeZero_isZero R _ _ _
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (((n ≫ δ₀) ≫ y) ≫ v) (f ≫ v) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetNativeConeComparison R CL DR V P Q
      (dgOdotMilnorCorner_complete R d) z hz).postcomp v
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((n ≫ δ₀) ≫ c) ((n ≫ δ₀) ≫ (y ≫ v)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (dgOdotMilnorCornerEvaluation_yoneda R d).symm (n ≫ δ₀)
  have hn' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((n ≫ δ₀) ≫ (y ≫ v)) (f ≫ v) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq hn (Category.assoc _ _ _) rfl
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (n ≫ δ₀ ≫ c) (f ≫ v) :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (hy.trans hn') (Category.assoc _ _ _) rfl
  exact h₀.trans (h₁.trans h₂)

def dgGluingOriginalLaxConeComparisonInput : DGOdotMilnorOriginalLaxConeComparisonInput R d :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingOriginalLaxComparisonInput R d).withCone R d (dgGluingOriginalInputConeIso R d)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
