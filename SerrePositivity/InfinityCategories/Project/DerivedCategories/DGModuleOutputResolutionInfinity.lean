module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionSection
/-!
概要：任意の dg 加群値関手の出力を、実分解 dg 圏を通じて半自由模型の実 ∞ 関手へ運ぶ。
方針：実入力射影の全 nerve 同値の逆と、実半自由出力射影の dg nerve を合成する。
規約：対象ごとの分解選択だけで済ませず、全単体上の関手と全関手比較同型を構成する。
使われ方：β5 の出力の射影性を仮定しない Hom の ∞ 関手化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 半自由出力の対象だけを共通宇宙へ上げた、同じ実出力 dg 射影。 -/
def dgModuleFunctorResolutionReplacementLift :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacement R C E F).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) w, v} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))
/-- 任意の dg 関手の実出力分解を、全単体を保持する半自由模型の ∞ 関手へ移す。 -/
def dgModuleOutputResolutionInfinity :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) w} C) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) w, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleFunctorResolutionReplacementLift R C E F)
/-- 同じ実分解 dg 圏へ戻すと、構成した ∞ 関手は実半自由出力射影と全関手同型で一致する。 -/
def dgModuleOutputResolutionInfinity_comparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) ≫
      dgModuleOutputResolutionInfinity R C E F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleFunctorResolutionReplacementLift R C E F)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).homInvIso
  have he := h.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleFunctorResolutionReplacementLift R C E F))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceLift R C E F) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleFunctorResolutionReplacementLift R C E F))
    (𝟙 _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleFunctorResolutionReplacementLift R C E F)) at he
  simpa only [dgModuleOutputResolutionInfinity, Category.assoc, Category.id_comp] using he
end SerrePositivity.InfinityCategories.Project.DerivedCategories
