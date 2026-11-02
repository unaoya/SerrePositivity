module

public import SerrePositivity.InfinityCategories.F1B.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalCosliceSource

/-!
概要：任意の関手による全共変 Hom の比較を、同じ coslice の底上の射から構成する。
方針：left fibration の元の辺を straightening し、全表現可能関手の比較へ戻す。
規約：関手圏のホモトピー圏の射であり、値ごとの比較族だけではない。
使われ方：Ind 比較の生成対象から任意の対象への全 Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 底上の同じ全空間の射を、元の全分類図式の間の射へ写す。 -/
def leftClassificationHom {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (HomotopyCategory.mk (functorVertex (leftStraighteningInfinityDiagram p)) :
      hoFunctor.obj ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u})) ⟶
        HomotopyCategory.mk (functorVertex (leftStraighteningInfinityDiagram q)) := by
  let e := (leftFibrationInfinityEdge p q f hf).map (leftStraighteningInfinityMap B)
  exact SSet.Truncated.HomotopyCategory.homMk (e.ofEq
    (leftStraighteningInfinityDiagram_vertex p).symm
    (leftStraighteningInfinityDiagram_vertex q).symm).toTruncated

/-- 元の関手の coslice 作用を、元の標的 coslice の厳密な底変換へ因子化する。 -/
def cosliceComparisonOver {C D : SSet.{u}} (G : C ⟶ D) (x : C _⦋0⦌) :
    sliceUnder (SSet.yonedaEquiv.symm x) ⟶
      pullback (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G :=
  pullback.lift (sliceUnderPostcomp (SSet.yonedaEquiv.symm x) G)
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (sliceUnderPostcomp_projection _ _)

lemma cosliceComparisonOver_postcomp {C D : SSet.{u}} (G : C ⟶ D) (x : C _⦋0⦌) :
    cosliceComparisonOver G x ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G =
        sliceUnderPostcomp (SSet.yonedaEquiv.symm x) G := pullback.lift_fst _ _ _

lemma cosliceComparisonOver_projection {C D : SSet.{u}} (G : C ⟶ D) (x : C _⦋0⦌) :
    cosliceComparisonOver G x ≫
      pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G =
        sliceUnderProjection (SSet.yonedaEquiv.symm x) := pullback.lift_snd _ _ _

/-- 標的の同じ共変 Hom を、元の関手による像の点を持つ coslice の分類へ戻す。 -/
def covariantHomTargetCosliceIso {C D : SSet.{u}} [Quasicategory D]
    (G : C ⟶ D) (x : C _⦋0⦌) :
    FunctorIso (covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x))
      (leftStraighteningInfinityDiagram
        (sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G))) := by
  rw [SSet.yonedaEquiv_symm_comp]
  exact Compact.covariantRepresentableInfinity_cosliceIso _

/-- 元の共変表現可能関手から、標的の同じ共変表現可能関手の制限への全自然な射。 -/
def covariantHomComparison {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    (G : C ⟶ D) (x : C _⦋0⦌) :
    (HomotopyCategory.mk (functorVertex (covariantRepresentableInfinity x)) :
      hoFunctor.obj ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj SpaceInfinity.{u})) ⟶
        HomotopyCategory.mk (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map G ≫
          covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x))) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)
  have : LeftFibration (pullback.snd q G) :=
    ⟨leftFibrations.pullback_snd q G (LeftFibration.mem (p := q))⟩
  exact (Compact.covariantRepresentableInfinity_cosliceIso x).hom ≫
    leftClassificationHom p (pullback.snd q G) (cosliceComparisonOver G x)
      (cosliceComparisonOver_projection G x) ≫
    (leftStraighteningInfinityDiagram_baseChangeIso q G).inv ≫
    ((covariantHomTargetCosliceIso G x).precomp ((SSet.uliftFunctor.{u + 1, u}).map G)).inv

end SerrePositivity.InfinityCategories.F2.Presentable
