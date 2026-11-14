module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleDerivedFunctor
/-!
概要：半自由模型上の実導来関手の恒等と合成を、全関手同型で比較する。
方針：射影的模型の厳密な dg 関手の恒等・合成と、同じ比較同値の余単位を使う。
規約：高次随伴・全 coherence は別工程。使われ方：β5 の tensor の単位・合成の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E T : Type v)
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] [Small.{u} T]
omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] [_root_.SerrePositivity.DifferentialGraded.DGCategory R T] [Small.{u} T] in
/-- 恒等 dg 関手からの実導来関手は、全関手圏で恒等と同型。 -/
def dgModuleDerivedFunctor_id_iso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D D (DGFunctor.id (RightModule R D)) (fun _ h => h))
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D)) := by
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D D (DGFunctor.id (RightModule R D)) (fun _ h => h) =
      DGFunctor.id (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction_id R (RightModule R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor, hd, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id, Category.id_comp]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose.homInvIso
/-- 実導来関手の合成は、同じ二つの元の dg 関手の合成の実導来関手と全関手圏で同型。 -/
def dgModuleDerivedFunctor_comp_iso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R D) (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R (_root_.SerrePositivity.DifferentialGraded.RightModule R E) (_root_.SerrePositivity.DifferentialGraded.RightModule R T))
    (hF : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E (F.obj M))
    (hG : ∀ M, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R E M → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R T (G.obj M)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D E F hF ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R E T G hG)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor R D T (F.comp G) (fun M hM => hG _ (hF M hM))) := by
  have hd : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D T (F.comp G) (fun M hM => hG _ (hF M hM)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R E T G hG) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullFunctorRestriction_comp R (RightModule R D) (RightModule R E) F G _ _ _ hF hG
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R E).choose.invHomIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjective R D) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R D E F hF))
  have h := h₀.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveModuleFunctor R E T G hG) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToProjectiveNerve_isQCatEquivalence R T).choose.inv)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedFunctor, hd, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc,
    Category.comp_id] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
