module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionPrecomp
/-!
概要：共通対象宇宙の元の nerve 上で、入力前合成に沿う同じ実出力分解を比較する。
方針：対象宇宙の上げ下げの厳密等式を、指定逆からの全関手比較へ渡す。
規約：入力の Small 性と元の出力の射影性は不要。使われ方：二入力 Hom の制限比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A C : Type (max (u + 1) v w)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ入力の対象宇宙の上げ下げは、指定前合成を厳密に保つ。 -/
lemma dgUniverseLift_sourcePrecomp :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))) =
      H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A).comp
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v w, max (u + 1) w} R A).comp
        (H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C))))
    (G := H.comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C)) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown,
    _root_.SerrePositivity.InfinityCategories.dgObjectImageEvaluation, Category.comp_id, Category.id_comp, eqToHom_refl]
/-- 元の nerve の入力前合成に沿う、同じ実出力分解の全関手同型。 -/
def dgModuleOutputResolution_unliftedPrecompIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R A E (H.comp F))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R C) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F) := by
  have h := congrArg (fun G => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G)
    (dgUniverseLift_sourcePrecomp.{u, v, w} R A C H)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at h
  have e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolution_precompIso R A C E H F).precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v w, max (u + 1) w} R A))
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp] at e
  simpa only [← Category.assoc, h] using! e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
