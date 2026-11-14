module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.PerfectDownValueComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.NativeModels.NativeUniverseIso
public import SerrePositivity.KST.SConstruction.DGOdotMilnorCornerEvaluation
/-!
概要：元二脚の小 Perf 包含と固定入力の指定同値の間の全自然性を供給する。
方針：一般の下降・評価自然性を元の二つの厳密制限へ前合成する。
規約：指定左右入力同値を保持する。使われ方：元二脚の lax 全比較の代入。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory SSet DifferentialGraded KST.SConstruction _root_.SerrePositivity.KST.LocalizingInvariants

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R A B L
local notation "DR" => DGSmallPerfectArrowTarget R A C G
local notation "V" => DGOdotCorner R d
local notation "P" => dgSmallPerfectSquareLeftMap R A B C E L G p q
local notation "Q" => dgSmallPerfectSquareRightMap R A B C E L G p q

def dgGluingOriginalLaxCornerEquivalence :=
  (dgOdotMilnorCornerEnvelopeEquivalence R d).trans
    (dgOdotMilnorCornerPerfectValueEquivalence R d)

def dgGluingOriginalLaxLeftEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R CL)
    (dgKInputStableValue R (dgOdotLeftInput R d)).obj :=
  (dgSmallPerfectEnvelopeNerveEquivalence R B (DGSmallPerfectBase R A)
    (dgSmallPerfectEnvelopeExtensionFamily R A B Empty (dgSmallPerfectBaseFamily R A) L)).trans
      ((dgOdotMilnorLeftPerfectDownEquivalence R d).symm.trans
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d)).symm)

lemma dgGluingOriginalLaxLeftEquivalence_input :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R CL)).hom ≫
      (dgOdotMilnorLaxLeftInputEquivalence R d).inv =
        (dgGluingOriginalLaxLeftEquivalence R d).hom := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R CL)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R CL)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

def dgGluingOriginalLaxLeftLeg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P ≫ (dgGluingOriginalLaxCornerEquivalence R d).hom)
    ((dgGluingOriginalLaxLeftEquivalence R d).hom ≫ (dgOdotLowerExactMap R d).hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.perfectDownValueComparison R B E p
    (dgOdotMilnorLeftPerfectDownEquivalence R d)
    (dgOdotMilnorCornerPerfectDownEquivalence R d)
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d))
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d))
    rfl rfl rfl rfl
  have h' := h.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A B L))
  unfold dgOdotLowerExactMap
  rw [dgKInputNuMap_eq]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectSquareCornerInclusion R A B C E L G p q) ≫ _)
    ((dgGluingOriginalLaxLeftEquivalence R d).hom ≫ _)
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    dgSmallPerfectSquareLeftMap_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A B L) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R B E p)) ≫
      (dgOdotMilnorCornerPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d)).inv)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A B L) ≫
      (dgOdotMilnorLeftPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d)).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.left))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower))))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm] using h'

def dgGluingOriginalLaxRightEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R DR)
    (dgKInputStableValue R (dgOdotRightInput R d)).obj :=
  (dgSmallPerfectEnvelopeNerveEquivalence R C (DGSmallPerfectBase R A)
    (dgSmallPerfectEnvelopeExtensionFamily R A C Empty (dgSmallPerfectBaseFamily R A) G)).trans
      ((dgOdotMilnorRightPerfectDownEquivalence R d).symm.trans
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d)).symm)

lemma dgGluingOriginalLaxRightEquivalence_input :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R DR)).hom ≫
      (dgOdotMilnorLaxRightInputEquivalence R d).inv =
        (dgGluingOriginalLaxRightEquivalence R d).hom := by
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R DR)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNativeUniverseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R DR)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

def dgGluingOriginalLaxRightLeg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q ≫ (dgGluingOriginalLaxCornerEquivalence R d).hom)
    ((dgGluingOriginalLaxRightEquivalence R d).hom ≫ (dgOdotUpperExactMap R d).hom) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.perfectDownValueComparison R C E q
    (dgOdotMilnorRightPerfectDownEquivalence R d)
    (dgOdotMilnorCornerPerfectDownEquivalence R d)
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d))
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d))
    rfl rfl rfl rfl
  have h' := h.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A C G))
  unfold dgOdotUpperExactMap
  rw [dgKInputNuMap_eq]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectSquareCornerInclusion R A B C E L G p q) ≫ _)
    ((dgGluingOriginalLaxRightEquivalence R d).hom ≫ _)
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
    dgSmallPerfectSquareRightMap_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A C G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension R C E q)) ≫
      (dgOdotMilnorCornerPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d)).inv)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectArrowTargetInclusion R A C G) ≫
      (dgOdotMilnorRightPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d)).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction R
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.corner))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper))))
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.trans, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.symm] using h'

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
