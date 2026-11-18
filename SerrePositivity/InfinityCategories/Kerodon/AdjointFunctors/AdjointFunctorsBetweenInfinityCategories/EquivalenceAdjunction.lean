module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition

/-!
概要：指定された準圏の同値の逆射と単位を、そのまま随伴へ組み直す。
方針：同じ可逆二胞体を双圏へ表示し、Mathlib の余単位の補正を適用する。
使われ方：HTT 5.2.2.8、Kerodon §6.2（Tag 02EH）の site 同値に沿う反射の輸送。
規約：新しい逆関手は選ばず、元の同値の homInvIso の逆を単位に使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

local instance equivalenceAdjunctionHomCategory (A B : SSet.QCat.{u}) :
    Category.{u} (A ⟶ B) := SSet.QCat.bicategory.homCategory A B

/-- 既存の全関手同型を、同じ二胞体の包みを持つ双圏の同型へ戻す。 -/
def functorIsoToQcatIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G : X ⟶ Y} (e : FunctorIso F G) : qcatMap F ≅ qcatMap G where
  hom := (qcatCellEquiv F G).symm e.hom
  inv := (qcatCellEquiv G F).symm e.inv
  hom_inv_id := by
    apply (qcatHomFunctor X Y).map_injective
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  inv_hom_id := by
    apply (qcatHomFunctor X Y).map_injective
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

/-- 同じ逆射と指定した可逆単位による、同値の随伴表示。 -/
def equivalenceAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (e : QCatEquivalence X Y) : QCatAdjunction e.hom e.inv :=
  (Bicategory.Equivalence.mkOfAdjointifyCounit
    (functorIsoToQcatIso e.homInvIso.symm) (functorIsoToQcatIso e.invHomIso)).adj

/-- 右随伴間の指定した全関手同型を、mate により左随伴の全関手同型へ戻す。 -/
def adjointFunctorIsoOfRightIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F F' : X ⟶ Y} {G G' : Y ⟶ X}
    (a : QCatAdjunction F G) (b : QCatAdjunction F' G') (e : FunctorIso G G') :
    FunctorIso F F' :=
  qcatIsoToFunctorIso
    (((Bicategory.conjugateIsoEquiv a b).symm (functorIsoToQcatIso e)).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
