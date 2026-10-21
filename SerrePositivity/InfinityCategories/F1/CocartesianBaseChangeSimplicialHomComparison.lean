module

public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeSimplicialHomPath
public import SerrePositivity.InfinityCategories.F1.IntervalHomPathMapNaturality

/-!
概要：元の比較 path の同じ Hom を、底で制限した同じ比較 path の Hom へ写す。
方針：元の図式の前合成を可逆 path の Hom へ作用させる。
規約：既存の元の Hom 比較空間と全高次の作用を保持する。
使われ方：既存の元の Hom 輸送の底の制限に関する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {D C : Type u} [Category.{u} D] [Category.{u} C]
  {A : SSet.{u + 1}} (a : A ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve D)) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二つの fibration での、底で制限した同じ比較 path の全 Hom。 -/
def cocartesianBaseChangeSimplicialHomComparisonSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeSimplicialHomPath a k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSimplicialHomPath a k).app _ (coherentNerveVertex q))

/-- 元の同じ制限した比較 Hom は Kan 複体。 -/
instance cocartesianBaseChangeSimplicialHomComparisonSpace_kanComplex :
    KanComplex (cocartesianBaseChangeSimplicialHomComparisonSpace a k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeSimplicialHomPath a k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeSimplicialHomPath a k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 既存の元の比較 Hom に、同じ底の前合成を作用させる。 -/
def cocartesianBaseChangeSimplicialHomMap :
    cocartesianBaseChangeHomComparisonSpace k p q ⟶
      cocartesianBaseChangeSimplicialHomComparisonSpace a k p q :=
  intervalHomFamilyProjection (cocartesianBaseChangeHomPath k)
    (equivalencePathMap
      ((pre a).app CatInfinity.{u}))
    (cocartesianBaseChangeSimplicialHomPath a k) rfl (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ制限は、元の可逆 path の Hom への同じ後合成そのもの。 -/
lemma cocartesianBaseChangeSimplicialHomMap_eq_post :
    cocartesianBaseChangeSimplicialHomMap a k p q = intervalMappingPost
      (equivalencePathMap
        ((pre a).app CatInfinity.{u}))
      ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex p))
      ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex q)) := by
  unfold cocartesianBaseChangeSimplicialHomMap intervalHomFamilyProjection
    cocartesianBaseChangeSimplicialHomPath
  exact intervalMappingPostOfEq_refl _ _ _

end SerrePositivity.InfinityCategories
