module

public import SerrePositivity.InfinityCategories.F1B.KanInitialBoundaryMappingSpace
public import SerrePositivity.InfinityCategories.F1B.MappingSpaceHom

/-!
概要：相対始点境界充填からホモトピー圏の各 Hom の全単射を得る。
方針：右 pinched 写像空間のホモトピー同値を π₀ と Hom の自然な対応で移す。
規約：全ての対象からの充満忠実性を仮定せず、指定された始点だけを使う。
使われ方：Kan 図式の点ごとの普遍性を大域的な自然変換の普遍性へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：相対始点境界を充填する点からのホモトピー圏の Hom の作用は全単射。
方針：写像空間の同値による Hom 対応が元の射のホモトピー圏の作用と一致することを使う。
規約：充満忠実性を全ての始点に仮定しない。
使われ方：局所 Kan 条件から得た大域的な制限の Hom 普遍性。 -/
lemma kanHoFunctorMap_bijective_of_initialBoundary {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) (x y : E _⦋0⦌)
    (hx : InitialBoundaryLifting p x) : Function.Bijective
      ((hoFunctor.map p).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
        (SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) x) ⟶
          SSet.HomotopyCategory.mk (p.app (Opposite.op ⦋0⦌) y))) := by
  have he := mappingSpaceHomMap_bijective (pinchedHomMap p x y)
    (kanPinchedHomMap_equivalence_of_initialBoundary p x y hx)
  have hmap : mappingSpaceHomMap (pinchedHomMap p x y) =
      ((hoFunctor.map p).toFunctor.map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) → _) :=
    funext (mappingSpaceHomMap_functor p x y)
  rw [hmap] at he
  exact he

end SerrePositivity.InfinityCategories.F1B
