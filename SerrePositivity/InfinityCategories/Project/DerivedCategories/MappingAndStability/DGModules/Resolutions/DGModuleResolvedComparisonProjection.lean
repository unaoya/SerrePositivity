module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionComparisonProjection
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FunctorIsoArrowTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorIsoWhiskerHEq
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolvedSectionIso
/-!
概要：元の入力切断の同じ比較同型の底への像を、端点輸送も含めて回収する。
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
/-- 元の入力比較同型は、同じ分解 nerve 同値の指定比較と HEq。 -/
lemma dgModuleResolvedProjectionSectionIso_heq :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).homInvIso := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso
  dsimp only [_root_.id]
  simp only [eq_mp_eq_cast, cast_heq]
/-- 元の入力射影と指定切断の同じ比較は、入力射影で恒等となる。 -/
lemma dgModuleResolvedProjectionSectionIso_projection_arrow :
    Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F))).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F))))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F)
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C)
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedProjectionSectionIso R C E F
  have hf : Q.hom ≫ Q.inv = P ≫ (U ≫ Q.inv) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) ≫ Q.inv = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, Category.assoc]
  have hh := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq Q.homInvIso a hf rfl
    (dgModuleResolvedProjectionSectionIso_heq R C E F) P
  have ha := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.functorIso_hom_arrow_of_heq (a.postcomp P) (Q.homInvIso.postcomp P)
    (congrArg (fun f ↦ f ≫ P) hf.symm) rfl hh
  exact ha.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionComparison_projection_arrow R C E F)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
