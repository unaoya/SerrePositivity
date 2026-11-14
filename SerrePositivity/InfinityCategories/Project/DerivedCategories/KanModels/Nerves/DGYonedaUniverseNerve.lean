module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGUniverseNerveFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGModuleNerveZero
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # dg Yoneda の全加群圏への実際の nerve

概要：小さい元の dg 圏から全 dg 加群圏への Yoneda を共通宇宙の単体的写像として構成。
方針：異なる対象宇宙を明示的に持ち上げ、全 Hom 複体の Yoneda 同型を適用する。
規約：像をラベル付き代表部分へ制限していない。使われ方：前三角 dg 圏の安定性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- dg Yoneda を全加群の nerve への実写像として共通宇宙で読む。 -/
def dgYonedaUniverseNerve :
    (SSet.uliftFunctor.{max (u + 1) v, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) ⟶
      (SSet.uliftFunctor.{v, max (u + 1) v}).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap (dgYoneda A D)

/-- 全加群 nerve への dg Yoneda は実写像空間で充満忠実。 -/
lemma dgYonedaUniverseNerve_isFullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (dgYonedaUniverseNerve A D) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveUniverseMap_isFullyFaithful_of_homIso
  intro x y
  change IsIso (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y)
  unfold _root_.SerrePositivity.DifferentialGraded.yonedaHom
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
