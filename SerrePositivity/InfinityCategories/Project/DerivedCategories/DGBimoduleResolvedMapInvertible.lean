module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionStrictNatTransInvertible
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.DifferentialGraded.Bimodule.Value
/-!
概要：同じ双加群射の像と準同型性を、実分解後の可逆性へ接続する。
方針：元の評価射・全 Hom 自然性・型付きの射の一致を保持する。
規約：出力の射影性と原 Hom の平坦性は不要。使われ方：模型変更の全自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet DifferentialGraded MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso
    (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
    {P Q : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory R E C} (f : P ⟶ Q)
    (hf : _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso R E C f) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleCategory.underlying R E C P).toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (BimoduleCategory.underlying R E C Q).toFunctor)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E)))
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBimoduleFunctorHomFunctor R E C).map f)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolution_strictNatTrans_isIso_of_quasiIso R C E f.val f.property
    (fun x => _root_.SerrePositivity.DifferentialGraded.BimoduleCategory.quasiIso_evaluation R E C hf x)
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
