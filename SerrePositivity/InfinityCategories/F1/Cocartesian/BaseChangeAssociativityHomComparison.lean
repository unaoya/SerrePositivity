module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityHomVertices
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalNaturality

/-!
概要：元の結合比較 path の全 Hom と、元の全相対 Hom の作用。
方針：同じ比較 path への coherent な区間 Hom の後合成を使う。
規約：既存の元の結合比較辺と全高次の族を保持する。
使われ方：第二面の Hom 輸送の分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))

/-- 元の二つの fibration での同じ結合比較 path の間の全 Hom。 -/
def cocartesianBaseChangeAssociativityHomComparisonSpace : SSet.{u + 1} :=
  intervalMappingSpace
    ((cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex q))

/-- 同じ結合比較 Hom は Kan 複体。 -/
instance cocartesianBaseChangeAssociativityHomComparisonSpace_kanComplex :
    KanComplex (cocartesianBaseChangeAssociativityHomComparisonSpace l k p q) := by
  change KanComplex (intervalMappingSpace
    ((cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex p))
    ((cocartesianBaseChangeAssociativityHomPath l k).app _ (coherentNerveVertex q)))
  infer_instance

/-- 元の全相対 Hom の core を、元の同じ結合比較 Hom へ写す。 -/
def cocartesianBaseChangeAssociativityHomComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      cocartesianBaseChangeAssociativityHomComparisonSpace l k p q :=
  coherentHomIntervalComparison p q ≫ intervalMappingPost
    (cocartesianBaseChangeAssociativityHomPath l k) (coherentNerveVertex p) (coherentNerveVertex q)

end SerrePositivity.InfinityCategories
