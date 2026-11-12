module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactorNaturality
/-!
概要：元の resolved 前合成の合成則を、明示した nerve 合成の端点輸送の下で等式にする。
方針：同じ型付き一致の両端だけを輸送する。
規約：元の指定比較を変更しない。使われ方：指定合成子内の前合成比較の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B C : Type (max (u + 1) v))
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の二段前合成則は、同じ nerve 合成の端点輸送を明示すれば等式になる。 -/
lemma dgModuleResolvedInfinity_precompIso_comp (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (J : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C)
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A C E (H.comp J) F) rfl
      (congrArg (fun m => m ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C E F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp H J)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R A B E H (J.comp F) ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso R B C E J F).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) := by
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_precompIso_comp_heq R A B C E H J F))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
