module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.RelativePrecompositionEquivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.F1B.CocartesianScaffold.ArbitraryBaseChange

/-!
概要：任意の部分底上で、元の全相対 Hom を同じ universal scaffold の相対 Hom と比較する。
方針：既存の任意底変換後の scaffold 同値を、元の標的への相対前合成と core に移す。
規約：元の全空間・全相対 Hom と同じ前合成を保持し、部分底の充填性は要求しない。
使われ方：境界固定の指定辺保存 Hom の比較を、同じ全相対 Hom から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) (q : F ⟶ nerve C)

/-- 元の universal scaffold の同じ底上の射。 -/
def cocartesianScaffoldOverMap :
    Over.mk (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ⟶
      Over.mk p := Over.homMk (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold p) (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_projection p)

/-- 部分底へ引き戻した同じ scaffold の、元の底上の射。 -/
def cocartesianScaffoldPullbackOverMap (a : Over (nerve C)) :
    Over.mk (pullback.snd a.hom
      (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ≫
        simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ⟶
    Over.mk (pullback.snd a.hom p ≫ p) :=
  Over.homMk
    (pullback.lift
      (pullback.fst a.hom
        (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)))
      (pullback.snd a.hom
        (simplicialReplacementProjection (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p)) ≫
          SerrePositivity.InfinityCategories.cocartesianUniversalScaffold p) (by
        rw [Category.assoc, SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_projection]
        exact pullback.condition)) (by
      dsimp only [Over.mk_hom]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc,
        SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_projection])

/-- 任意の部分底上でも、同じ scaffold の実際の射は前合成同値。 -/
lemma cocartesianScaffoldPullbackOverMap_isPrecompositionEquivalence
    [CocartesianFibration p] (a : Over (nerve C)) :
    IsPrecompositionEquivalence (cocartesianScaffoldPullbackOverMap p a).left := by
  change IsPrecompositionEquivalence (overPullbackMap
    (Over.homMk (U := Over.mk (simplicialReplacementProjection
      (SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram p))) (V := Over.mk p)
      (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold p) (SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_projection p)) (Over.mk a.hom))
  exact SerrePositivity.InfinityCategories.cocartesianUniversalScaffold_overPullback_isPrecompositionEquivalence p a.hom

/-- 元の全相対 Hom を、部分底へ引き戻した同じ scaffold へ前合成する。 -/
def cocartesianScaffoldPullbackRawHomPre (a : Over (nerve C)) :=
  relativeFunctorOverPre q (cocartesianScaffoldPullbackOverMap p a)

/-- 同じ全相対 Hom の前合成は、任意の部分底で同値。指定辺条件への制限は別途行う。 -/
lemma cocartesianScaffoldPullbackRawHomPre_isQCatEquivalence
    [CocartesianFibration p] [CocartesianFibration q] (a : Over (nerve C)) :
    IsQCatEquivalence (cocartesianScaffoldPullbackRawHomPre p q a) :=
  relativeFunctorOverPre_isQCatEquivalence_of_cocartesian q _
    (cocartesianScaffoldPullbackOverMap_isPrecompositionEquivalence p a)

/-- 同じ元の相対 Hom の core に作用する、同じ scaffold の前合成。 -/
def cocartesianScaffoldPullbackRawCorePre (a : Over (nerve C)) :=
  quasicategoryCoreMap (cocartesianScaffoldPullbackRawHomPre p q a)

/-- 元の全相対 Hom の core の同じ前合成も、部分底の充填性を仮定せず同値。 -/
lemma cocartesianScaffoldPullbackRawCorePre_isQCatEquivalence
    [CocartesianFibration p] [CocartesianFibration q] (a : Over (nerve C)) :
    IsQCatEquivalence (cocartesianScaffoldPullbackRawCorePre p q a) :=
  (cocartesianScaffoldPullbackRawHomPre_isQCatEquivalence p q a).core

end SerrePositivity.InfinityCategories
