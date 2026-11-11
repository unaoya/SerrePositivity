module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedSourceSection
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open DifferentialGraded MonoidalClosed
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 実入力射影の宇宙持ち上げと下げの合成は、元の dg 射影。 -/
lemma dgModuleFunctorResolutionSourceLift_comp_down :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R C) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R) (fun _ => rfl)
  intro x y
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift, EnrichedFunctor.comp_map,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown, _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation,
    Category.comp_id, eqToHom_refl]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
