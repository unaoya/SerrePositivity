module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.LaxComparisonEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.Size
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackEquivalenceSubcomplex
/-!
概要：元 dg gluing の中で、同じ導来 augmentation が可逆な対象の充満 dg 部分圏を取る。
方針：正本の全矢印族で対象条件を指定し、Hom 複体・単位・合成をそのまま制限する。
規約：元の二対象と augmentation を保持する。準同型判定は OrdinaryPullbackQuasiIso で接続する。
使われ方：G-1 f の通常 pullback 比較と同じ部分圏を零化する平坦 Verdier 商に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
def dgGluingPullbackProperty (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedAugmentationArrowFamily R C D M).app
    (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))
abbrev DGGluingPullbackObject :=
  DGFullSubcategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgGluingPullbackProperty R C D M)
def dgGluingPullbackInclusion :
    DGFunctor R (DGGluingPullbackObject R C D M) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  _root_.SerrePositivity.DifferentialGraded.dgFullSubcategoryInclusion R _ _
lemma dgGluingPullbackProperty_iff_laxVertex (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    dgGluingPullbackProperty R C D M X ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsLaxEquivalenceVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M).app (Opposite.op ⦋0⦌)
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) := by
  change _ ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison R C D M ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedYoneda.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M)).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedNerveLaxComparison_arrow]
  rfl
lemma dgGluingPullbackInclusion_hom (X Y : DGGluingPullbackObject R C D M) :
    (dgGluingPullbackInclusion R C D M).map X Y =
      𝟙 (homObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) X.val Y.val) := rfl
instance dgGluingPullbackObject_small [Small.{u} D] :
    Small.{u} (DGGluingPullbackObject R C D M) := inferInstance
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
