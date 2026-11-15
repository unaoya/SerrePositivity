module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EquivalenceAdjunction

/-!
概要：指定同値の既存の随伴表示について、単位と余単位の可逆性を回収する。
方針：元の同じ双圏同値の unit・counit の同型を読む。
使われ方：HTT §5.2.2、Kerodon §6.2（Tag 02EH）の指定正方形の mate の可逆性。
規約：逆射・単位を選び直さず、既存の equivalenceAdjunction を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

local instance equivalenceAdjunctionIsoDataHomCategory (A B : SSet.QCat.{u}) :
    Category.{u} (A ⟶ B) := SSet.QCat.bicategory.homCategory A B

/-- 元の equivalenceAdjunction の内部の、同じ指定双圏同値を名前で読む。 -/
def equivalenceAdjunctionEquivalence {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : Bicategory.Equivalence (qcatOf X) (qcatOf Y) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (a := qcatOf X) (b := qcatOf Y) (f := qcatMap e.hom) (g := qcatMap e.inv)
    (functorIsoToQcatIso e.homInvIso.symm) (functorIsoToQcatIso e.invHomIso)

/-- 同じ同値の随伴の単位は、元の指定 homInvIso の逆の同型である。 -/
lemma equivalenceAdjunction_unit_isIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : IsIso (equivalenceAdjunction e).unit := by
  change IsIso (equivalenceAdjunctionEquivalence e).unit.hom
  infer_instance

/-- 同じ随伴表示の余単位も、既存の補正された可逆二胞体である。 -/
lemma equivalenceAdjunction_counit_isIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : IsIso (equivalenceAdjunction e).counit := by
  change IsIso (equivalenceAdjunctionEquivalence e).counit.hom
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
