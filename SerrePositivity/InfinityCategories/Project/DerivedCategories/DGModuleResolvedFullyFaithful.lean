module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedProjectiveComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulCalculus

/-!
概要：κ 未満自由 sphere の実小代表族と、射影的代表集合の導来 ∞ 比較を構成する。
方針：小さい ordinal 添字と実直和表示、β5 の全関手比較を保持する。
規約：全共変 Hom による κ-compact 性や全 κ-compact 被覆はここでは結論しない。
使われ方：K-7 に供給する実 κ-compact dg 小模型の出発点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

lemma dgModuleResolvedInfinity_isFullyFaithful_of_projective_homIso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R D))
    (hF : ∀ x, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveProperty R D (F.obj x))
    (hHom : ∀ x y, IsIso (F.map x y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity R C D F) := by
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso F hHom
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_inclusionIso R C D F hF
  have hcomp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.isFullyFaithful_iff hi).mpr hf
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModulesInclusion_isFullyFaithful R D).cancel_right hcomp

end SerrePositivity.InfinityCategories.Project.DerivedCategories
