module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomWhiskering
/-!
概要：同じ augmentation の四角形を満たす模型射の導来像は選択によらない。
方針：元の出力模型比較を消去し、準同値への後合成の充満忠実性で反映する。
規約：指定比較を変更しない。使われ方：一般 cell 模型の選択整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPostcomp_injective_typed {X Y Z : SSet.{w}}
    [Quasicategory Y] [Quasicategory Z] {q : Y ⟶ Z} (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful q)
    {f g : X ⟶ Y} : Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful hq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
