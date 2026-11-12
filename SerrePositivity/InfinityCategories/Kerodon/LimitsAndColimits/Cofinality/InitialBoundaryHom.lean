module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceHom

/-!
概要：相対始点境界充填からホモトピー圏の各 Hom の全単射を得る。
方針：右 pinched 写像空間のホモトピー同値を π₀ と Hom の自然な対応で移す。
規約：全ての対象からの充満忠実性を仮定せず、指定された始点だけを使う。
使われ方：Kan 図式の点ごとの普遍性を大域的な自然変換の普遍性へ移す。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：相対始点境界を充填する点からのホモトピー圏の Hom の作用は全単射。
方針：写像空間の同値による Hom 対応が元の射のホモトピー圏の作用と一致することを使う。
規約：充満忠実性を全ての始点に仮定しない。
使われ方：局所 Kan 条件から得た大域的な制限の Hom 普遍性。 -/
lemma hoFunctorMap_bijective_of_initialBoundary {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (x y : E _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x) : Function.Bijective
      ((hoFunctor.map p).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
        (SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) x) ⟶
          SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) y))) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary p x y hx)
  have hmap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) =
      ((hoFunctor.map p).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) → _) :=
    funext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.mappingSpaceHomMap_functor p x y)
  rw [hmap] at he
  exact he

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
