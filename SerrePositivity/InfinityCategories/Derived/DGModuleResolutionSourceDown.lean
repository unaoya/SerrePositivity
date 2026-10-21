module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedSourceSection
/-!
概要：実入力射影の対象宇宙を下げると、元の同じ dg 射影に厳密に戻る。
方針：実 fiber の射影の恒等性と、同じ宇宙比較・端点輸送を使う。
規約：元の指定同型と実切断を保持する。使われ方：kernel の指定余単位の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open DifferentialGraded DGNerve MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
  (E : Type v) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 実入力射影の宇宙持ち上げと下げの合成は、元の dg 射影。 -/
lemma dgModuleFunctorResolutionSourceLift_comp_down :
    (dgModuleFunctorResolutionSourceLift R C E F).comp
      (dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) =
      dgModuleFunctorResolutionSource R C E F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [dgModuleFunctorResolutionSourceLift, EnrichedFunctor.comp_map,
    dgUniverseLiftUp, dgUniverseLiftDown, dgObjectImageEvaluation,
    Category.comp_id, eqToHom_refl]
end SerrePositivity.InfinityCategories
