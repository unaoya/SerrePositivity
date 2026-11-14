module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleOutputResolutionInfinity
/-!
概要：実出力移送の各値から、元の同じ実入力像への半自由分解を回収する。
方針：全単体上の厳密切断を零単体で評価し、同じ分解対象の augmentation を読む。
規約：入力は同型までではなく元の同じ対象。使われ方：D(R) 値 Hom の実複体との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ実切断が実入力 x に選ぶ、入力と半自由出力を持つ実分解対象。 -/
def dgModuleOutputResolutionObject (x : C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv.app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).obj x)))
/-- 厳密切断で回収した分解対象の入力は、元の同じ実対象。 -/
lemma dgModuleOutputResolutionObject_source (x : C) :
    (dgModuleOutputResolutionObject R C E F x).source = x := by
  have he := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv
    (f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).obj x))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence_inv_hom R C E F)
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).obj
    (dgModuleOutputResolutionObject R C E F x).source = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).obj x at he
  exact congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, max (u + 1) w} C ↦ t.label.down) he
/-- 同じ全 ∞ 関手が x へ与える実半自由出力。 -/
def dgModuleOutputResolutionValue (x : C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E :=
  (dgModuleOutputResolutionObject R C E F x).replacement
/-- 実出力分解の同じ augmentation を、厳密に元の実入力像へ戻す。 -/
def dgModuleOutputResolutionAugmentation (x : C) :
    ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgModuleOutputResolutionValue R C E F x).val ⟶
      ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj x) :=
  (dgModuleOutputResolutionObject R C E F x).augmentation ≫
    eqToHom (congrArg (fun y ↦ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj y))
      (dgModuleOutputResolutionObject_source R C E F x))
/-- 全実出力 ∞ 関手の頂点値は、同じ切断から回収した実半自由出力。 -/
lemma dgModuleOutputResolutionInfinity_vertex (x : C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R C).obj x)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).obj
      (dgModuleOutputResolutionValue R C E F x)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
