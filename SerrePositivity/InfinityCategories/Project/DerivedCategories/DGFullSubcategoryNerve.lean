module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorFullyFaithful
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # dg 充満部分圏の nerve の充満忠実性

概要：dg 充満部分圏の包含は実際の ∞ 写像空間で充満忠実。
方針：Hom 複体の恒等写像を一般の Hom 同型の判定へ渡す。
規約：h の充満忠実性だけに留めない。使われ方：β3 の表現可能部分圏と商の零化部分。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] (P : D → Prop)

/-- dg 充満部分圏の包含は ∞ 圏の nerve でも充満忠実。 -/
lemma dgFullSubcategoryInclusionNerve_isFullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A D P)) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_map_isFullyFaithful_of_homIso
  intro x y
  change IsIso (𝟙 (_root_.SerrePositivity.DifferentialGraded.homObject A D x.val y.val))
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories
