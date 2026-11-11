module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentityValueEquivalences

/-!
概要：恒等右面の固定 ν 差と、元の実 cone 全関手を指定評価の後で照合する。
方針：元の native／ν 自然性と同じ全像小模型の評価を合成する。
規約：全関手同型を保持する。Sp の恒等 lax 差との比較は別工程。
使われ方：D2 に依頼する cone 差比較の固定 ν 側を具体化する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => DGOdotMilnorIdentityBase R d
local notation "L" => DGOdotMilnorIdentityGluing R d
local notation "D" => DGOdotMilnorIdentityDifference R d
local notation "F" => dgHomGluingConeFunctor R (C) (C) (C)
  (DGFunctor.id (C)) (DGFunctor.id (C))
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) := dgOdotMilnorIdentityBase_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (L) := dgOdotMilnorIdentityGluing_pretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (D) := dgOdotMilnorIdentityDifference_pretriangulated R d

/-- 概要：同じ固定 ν の実差は、指定終域同値の後で元の全 cone 関手を回収する。
方針：native／ν 自然性と全像包含の厳密回収を全関手同型として貼る。
規約：全 Hom 作用と元の実 cone 対象族を保持する。
使われ方：恒等 lax 差と比較する実右辺の固定評価。 -/
def dgOdotMilnorIdentityConeValueComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (dgKNativeValueComparison R (L) ≫
      ((dgKInputNuMap R (dgOdotMilnorIdentityDifferenceInputMap R d)).hom ≫
        (dgOdotMilnorIdentityDifferenceValueEquivalence R d).hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) ≫ (dgKNativePerfectValueEquivalence R (C)).hom) := by
  let e := dgOdotMilnorIdentityDifferenceValueEquivalence R d
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorIdentityDifference R d)
  let n := dgKNativeValueComparison R (D)
  let P := (dgSmallPerfectEnvelopeNerveEquivalence R (C) (L) (F).obj).hom
  let V := (dgKNativePerfectValueEquivalence R (C)).hom
  have h₁ := (dgOdotMilnorIdentityDifference_nu_comparison R d).postcomp e.hom
  have h₂ := (dgOdotMilnorIdentityDifferenceValueEquivalence_native R d).precomp f
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₁ rfl (Category.assoc f n e.hom)).trans h₂
  have he : f ≫ P = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectFunctorImageLift R (L) (C) (F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgSmallPerfectEnvelopeInclusion R (C) (L) (F).obj) = _
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, dgSmallPerfectFunctorImageLift_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq h₃ (Category.assoc _ _ _)
    ((Category.assoc f P V).symm.trans (congrArg (fun k => k ≫ V) he))
end SerrePositivity.KST.SConstruction
