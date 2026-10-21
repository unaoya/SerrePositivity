module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedPrecomposition
/-!
概要：元の出力分解と変更同型の指定値を、同じ raw 出力射影へ回収する。
方針：出力宇宙の上げ下げと指定出力比較の後合成則だけを使う。
規約：元の入力切断と変更比較を保持。使われ方：導来射作用との共役式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E]
lemma dgModuleFunctorResolutionReplacementLift_down
    (F : DGFunctor R C (RightModule R E)) :
    dgNerve.map (dgModuleFunctorResolutionReplacementLift R C E F) ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E)) =
      dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) := by
  have h := congrArg (fun L => dgNerve.map L)
    (dgUniverseLiftUp_comp_down.{u, max (u + 1) v, max (u + 1) v} R
      (SemifreeDGModules R E))
  simp only [dgNerve.map_comp, dgNerve.map_id] at h
  simp only [dgModuleFunctorResolutionReplacementLift, dgNerve.map_comp,
    Category.assoc, h, Category.comp_id]
lemma dgModuleOutputResolutionInfinity_down_eq
    (F : DGFunctor R C (RightModule R E)) :
    dgModuleOutputResolutionInfinity R C E F ≫
      dgNerve.map (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
        (SemifreeDGModules R E)) =
      (dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
        dgNerve.map (dgModuleFunctorResolutionReplacement R C E F) := by
  rw [dgModuleOutputResolutionInfinity, Category.assoc,
    dgModuleFunctorResolutionReplacementLift_down]
end SerrePositivity.InfinityCategories
