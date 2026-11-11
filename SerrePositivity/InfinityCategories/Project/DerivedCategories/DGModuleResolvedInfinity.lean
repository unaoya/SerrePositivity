module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionAugmentation
/-!
概要：共通対象宇宙の任意の dg 加群値関手を、元の実半自由模型へ移す。
方針：実出力分解の前後に対象宇宙だけの上げ下げを合成する。
規約：出力の射影性も入力の小ささも不要。使われ方：一般双加群作用とその比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 実出力分解を、元の入力の dg nerve から元の半自由模型への実 ∞ 関手にする。 -/
def dgModuleResolvedInfinity : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionInfinity R C E F ≫
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, max (u + 1) v, max (u + 1) v} R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E))
end SerrePositivity.InfinityCategories.Project.DerivedCategories
