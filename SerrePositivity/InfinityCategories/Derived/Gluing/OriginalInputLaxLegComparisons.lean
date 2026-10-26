module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PerfectDownValueComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUniverseIso
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open Derived.Gluing
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R d.source
local notation "B" => dgAlgebraCategory R d.left
local notation "C" => dgAlgebraCategory R d.right
local notation "E" => dgAlgebraCategory R d.corner
local notation "L" => dgAlgebraMap R d.top
local notation "G" => dgAlgebraMap R d.side
local notation "p" => dgAlgebraMap R d.lower
local notation "q" => dgAlgebraMap R d.upper
local notation "CL" => DGSmallPerfectArrowTarget R A B L
local notation "DR" => DGSmallPerfectArrowTarget R A C G
local notation "V" => DGOdotCorner R d
local notation "P" => dgSmallPerfectSquareLeftMap R A B C E L G p q
local notation "Q" => dgSmallPerfectSquareRightMap R A B C E L G p q

def dgGluingOriginalLaxCornerEquivalence :=
  (dgOdotMilnorCornerEnvelopeEquivalence R d).trans
    (dgOdotMilnorCornerPerfectValueEquivalence R d)

def dgGluingOriginalLaxLeftEquivalence : QCatEquivalence (dgNerve R CL)
    (dgKInputStableValue R (dgOdotLeftInput R d)).obj :=
  (dgSmallPerfectEnvelopeNerveEquivalence R B (DGSmallPerfectBase R A)
    (dgSmallPerfectEnvelopeExtensionFamily R A B Empty (dgSmallPerfectBaseFamily R A) L)).trans
      ((dgOdotMilnorLeftPerfectDownEquivalence R d).symm.trans
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d)).symm)

lemma dgGluingOriginalLaxLeftEquivalence_input :
    (dgGluingNativeUniverseIso (dgNerve R CL)).hom ≫
      (dgOdotMilnorLaxLeftInputEquivalence R d).inv =
        (dgGluingOriginalLaxLeftEquivalence R d).hom := by
  change (dgGluingNativeUniverseIso (dgNerve R CL)).hom ≫
    (dgGluingNativeUniverseIso (dgNerve R CL)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

def dgGluingOriginalLaxLeftLeg : FunctorIso
    (dgNerve.map P ≫ (dgGluingOriginalLaxCornerEquivalence R d).hom)
    ((dgGluingOriginalLaxLeftEquivalence R d).hom ≫ (dgOdotLowerExactMap R d).hom) := by
  have h := perfectDownValueComparison R B E p
    (dgOdotMilnorLeftPerfectDownEquivalence R d)
    (dgOdotMilnorCornerPerfectDownEquivalence R d)
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d))
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d))
    rfl rfl rfl rfl
  have h' := h.precomp (dgNerve.map (dgSmallPerfectArrowTargetInclusion R A B L))
  unfold dgOdotLowerExactMap
  rw [dgKInputNuMap_eq]
  change FunctorIso (dgNerve.map P ≫
      dgNerve.map (dgSmallPerfectSquareCornerInclusion R A B C E L G p q) ≫ _)
    ((dgGluingOriginalLaxLeftEquivalence R d).hom ≫ _)
  rw [← Category.assoc, ← dgNerve.map_comp,
    dgSmallPerfectSquareLeftMap_inclusion, dgNerve.map_comp]
  change FunctorIso
    ((dgNerve.map (dgSmallPerfectArrowTargetInclusion R A B L) ≫
        dgNerve.map (perfectDGExtension R B E p)) ≫
      (dgOdotMilnorCornerPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d)).inv)
    ((dgNerve.map (dgSmallPerfectArrowTargetInclusion R A B L) ≫
      (dgOdotMilnorLeftPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotLeftInput R d)).inv) ≫
      dgNerve.map (presentedPerfectDGAction R
        (DGUniverseLift (dgAlgebraCategory R d.left))
        (DGUniverseLift (dgAlgebraCategory R d.corner))
        (dgUniverseLiftFunctor (dgAlgebraMap R d.lower))))
  simpa only [FunctorIso, Category.assoc, QCatEquivalence.trans, QCatEquivalence.symm] using h'

def dgGluingOriginalLaxRightEquivalence : QCatEquivalence (dgNerve R DR)
    (dgKInputStableValue R (dgOdotRightInput R d)).obj :=
  (dgSmallPerfectEnvelopeNerveEquivalence R C (DGSmallPerfectBase R A)
    (dgSmallPerfectEnvelopeExtensionFamily R A C Empty (dgSmallPerfectBaseFamily R A) G)).trans
      ((dgOdotMilnorRightPerfectDownEquivalence R d).symm.trans
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d)).symm)

lemma dgGluingOriginalLaxRightEquivalence_input :
    (dgGluingNativeUniverseIso (dgNerve R DR)).hom ≫
      (dgOdotMilnorLaxRightInputEquivalence R d).inv =
        (dgGluingOriginalLaxRightEquivalence R d).hom := by
  change (dgGluingNativeUniverseIso (dgNerve R DR)).hom ≫
    (dgGluingNativeUniverseIso (dgNerve R DR)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]
  rfl

def dgGluingOriginalLaxRightLeg : FunctorIso
    (dgNerve.map Q ≫ (dgGluingOriginalLaxCornerEquivalence R d).hom)
    ((dgGluingOriginalLaxRightEquivalence R d).hom ≫ (dgOdotUpperExactMap R d).hom) := by
  have h := perfectDownValueComparison R C E q
    (dgOdotMilnorRightPerfectDownEquivalence R d)
    (dgOdotMilnorCornerPerfectDownEquivalence R d)
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d))
    (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d))
    rfl rfl rfl rfl
  have h' := h.precomp (dgNerve.map (dgSmallPerfectArrowTargetInclusion R A C G))
  unfold dgOdotUpperExactMap
  rw [dgKInputNuMap_eq]
  change FunctorIso (dgNerve.map Q ≫
      dgNerve.map (dgSmallPerfectSquareCornerInclusion R A B C E L G p q) ≫ _)
    ((dgGluingOriginalLaxRightEquivalence R d).hom ≫ _)
  rw [← Category.assoc, ← dgNerve.map_comp,
    dgSmallPerfectSquareRightMap_inclusion, dgNerve.map_comp]
  change FunctorIso
    ((dgNerve.map (dgSmallPerfectArrowTargetInclusion R A C G) ≫
        dgNerve.map (perfectDGExtension R C E q)) ≫
      (dgOdotMilnorCornerPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotCornerInput R d)).inv)
    ((dgNerve.map (dgSmallPerfectArrowTargetInclusion R A C G) ≫
      (dgOdotMilnorRightPerfectDownEquivalence R d).inv ≫
        (presentedPerfectDGQCatEvaluationEquivalence R (dgOdotRightInput R d)).inv) ≫
      dgNerve.map (presentedPerfectDGAction R
        (DGUniverseLift (dgAlgebraCategory R d.right))
        (DGUniverseLift (dgAlgebraCategory R d.corner))
        (dgUniverseLiftFunctor (dgAlgebraMap R d.upper))))
  simpa only [FunctorIso, Category.assoc, QCatEquivalence.trans, QCatEquivalence.symm] using h'

end SerrePositivity.InfinityCategories
