module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeRestrictedHomPath
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalHomPathMapNaturality

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

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二つの fibration での、底で制限した同じ比較 path の全 Hom。 -/
def cocartesianBaseChangeRestrictedHomComparisonSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeRestrictedHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeRestrictedHomPath l k).app _ (coherentNerveVertex q))

/-- 元の同じ制限した比較 Hom は Kan 複体。 -/
instance cocartesianBaseChangeRestrictedHomComparisonSpace_kanComplex :
    KanComplex (cocartesianBaseChangeRestrictedHomComparisonSpace l k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeRestrictedHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeRestrictedHomPath l k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 既存の元の比較 Hom に、同じ底の前合成を作用させる。 -/
def cocartesianBaseChangeRestrictedHomMap :
    cocartesianBaseChangeHomComparisonSpace k p q ⟶
      cocartesianBaseChangeRestrictedHomComparisonSpace l k p q :=
  intervalHomFamilyProjection (cocartesianBaseChangeHomPath k)
    (equivalencePathMap
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}))
    (cocartesianBaseChangeRestrictedHomPath l k) rfl (coherentNerveVertex p) (coherentNerveVertex q)

/-- 同じ制限は、元の可逆 path の Hom への同じ後合成そのもの。 -/
lemma cocartesianBaseChangeRestrictedHomMap_eq_post :
    cocartesianBaseChangeRestrictedHomMap l k p q = intervalMappingPost
      (equivalencePathMap
        ((pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap l))).app CatInfinity.{u}))
      ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex p))
      ((cocartesianBaseChangeHomPath k).app _ (coherentNerveVertex q)) := by
  unfold cocartesianBaseChangeRestrictedHomMap intervalHomFamilyProjection
    cocartesianBaseChangeRestrictedHomPath
  exact intervalMappingPostOfEq_refl _ _ _

end SerrePositivity.InfinityCategories
