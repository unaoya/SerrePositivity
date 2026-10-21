module

public import SerrePositivity.InfinityCategories.F1.InvertibleFunctorEdgePath
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeJointComparisonIso
public import SerrePositivity.InfinityCategories.F1.CocartesianStraighteningHomInterval
public import SerrePositivity.InfinityCategories.F1.PreFiberKan

/-!
概要：元の底変換比較の同じ可逆辺の Hom を、分類 Hom 比較の共通の空間にする。
方針：同じ円柱を可逆 path の族へ移し、元の全相対 Hom の区間を後合成する。
規約：構成済みの同じ比較の辺を使い、同型の別の代表を選び直さない。
使われ方：底の制限側と底変換後の側の実際の Hom 作用の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)

/-- 元の底変換比較の同じ全円柱を保つ、元の全 fibration 上の可逆 path の族。 -/
def cocartesianBaseChangeHomPath :
    CocartesianFibrationInfinity (nerve C) ⟶
      equivalencePath (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D))) :=
  invertibleFunctorEdgePath (cocartesianBaseChangeJointComparisonEdge k).toTruncated
    (cocartesianBaseChangeJointComparisonEdge_isInvertible k)

/-- 同じ path の零端点は、元の分類主写像の同じ底の制限。 -/
lemma cocartesianBaseChangeHomPath_zero :
    cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 0 =
      cocartesianStraighteningCoherentMap C ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app CatInfinity.{u} :=
  invertibleFunctorEdgePath_zero _ _

/-- 同じ path の一端点は、元の底変換後の分類主写像。 -/
lemma cocartesianBaseChangeHomPath_one :
    cocartesianBaseChangeHomPath k ≫ equivalencePathEndpoint _ 1 =
      cocartesianFibrationInfinityBaseChange (nerveMap k) ≫ cocartesianStraighteningCoherentMap D :=
  invertibleFunctorEdgePath_one _ _

/-- 元の二つの fibration での同じ比較 path の間の全区間 Hom。 -/
def cocartesianBaseChangeHomComparisonSpace
    (p q : CocartesianFibrationCategory (nerve C)) : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex q))

/-- 元の比較 path の間の同じ Hom は、両端固定の Kan 複体。 -/
instance cocartesianBaseChangeHomComparisonSpace_kanComplex
    (p q : CocartesianFibrationCategory (nerve C)) :
    KanComplex (cocartesianBaseChangeHomComparisonSpace k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 元の全相対 Hom の core の同じ区間族を、同じ比較 path の Hom へ写す。 -/
def cocartesianBaseChangeHomComparison
    (p q : CocartesianFibrationCategory (nerve C)) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      cocartesianBaseChangeHomComparisonSpace k p q :=
  coherentHomComparison p q ≫
    pinchedHomToIntervalMappingSpace (coherentNerveVertex p) (coherentNerveVertex q) ≫
      intervalMappingPost (cocartesianBaseChangeHomPath k) (coherentNerveVertex p)
        (coherentNerveVertex q)

/-- 同じ比較作用の展開は、元の Hom の prism を同じ比較 path へ後合成したもの。 -/
lemma cocartesianBaseChangeHomComparison_uncurry
    (p q : CocartesianFibrationCategory (nerve C)) :
    intervalMappingUncurry (cocartesianBaseChangeHomComparison k p q) =
      rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison p q) ≫
        cocartesianBaseChangeHomPath k := by
  rw [cocartesianBaseChangeHomComparison, ← Category.assoc,
    intervalMappingPost_uncurry, pinchedHomToIntervalMappingSpace_uncurry]
  rfl

end SerrePositivity.InfinityCategories
