module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConjugateUnit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EquivalenceAdjunction

/-!
概要：既存の左随伴比較の全関手同型を、同じ指定単位の等式とともに読む。
方針：逆 conjugate の単位法則を二胞体の同じ表示へ移す。
使われ方：HTT §5.2.2、Kerodon §6.2（Tag 02EH）の site 同値と層化の単位の比較。
規約：比較同型・単位・随伴のいずれも選び直さない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

local instance adjointComparisonUnitHomCategory (A B : SSet.QCat.{u}) :
    Category.{u} (A ⟶ B) := SSet.QCat.bicategory.homCategory A B

/-- 同じ右随伴比較から作った元の全関手同型は、随伴の指定単位と整合する。 -/
lemma adjointFunctorIsoOfRightIso_unit {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G G' : Y ⟶ X}
    (a : QCatAdjunction F G) (b : QCatAdjunction F' G') (e : FunctorIso G G') :
    a.unit ≫ qcatMap F ◁ (functorIsoToQcatIso e).hom =
      b.unit ≫ (functorIsoToQcatIso (adjointFunctorIsoOfRightIso a b e)).inv ▷ qcatMap G' := by
  change a.unit ≫ qcatMap F ◁ (functorIsoToQcatIso e).hom =
    b.unit ≫ ((Bicategory.conjugateEquiv a b).symm (functorIsoToQcatIso e).hom) ▷ qcatMap G'
  exact bicategory_unit_conjugateEquiv_symm a b _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
