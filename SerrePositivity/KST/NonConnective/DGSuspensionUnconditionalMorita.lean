module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalMoritaCone
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionMoritaEquivalence

/-!
概要：新提供者の同じ実懸垂入力射は、元の主導来 Morita 射に対して全 ∞ 圏同値となる。
方針：D-S の実 cone 同値・perfect 核反映を、元の厳密商入力射を保つ下降同値へ代入する。
規約：全反復の構造辺自然性と K^{nc} の Morita 不変性は別工程。c4 の存在は推論しない。
使われ方：K-7 e の実 Morita 射の、一回の元の懸垂段での保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)
  [(dgDerivedExtension R A B (perfDGInputHomEquiv R A B f)).IsEquivalence]
local notation "s" => dgKappaUnconditionalStageProvider R κ hκ

/-- 同じ新提供者上で、元の厳密懸垂入力射を順射として保つ実商の Morita 同値。 -/
def dgKappaUnconditionalSuspensionMoritaEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKappaSuspensionInfinity R A (s A).cone)
      (dgKappaSuspensionInfinity R B (s B).cone) :=
  dgKappaSuspensionMoritaEquivalence R A B (s A).cone (s B).cone
    (dgKappaUnconditionalSuspensionMapData R κ hκ f)
    (dgKappaUnconditionalConeMap_isQCatEquivalence_of_morita R κ hκ f)
    (fun M hM => (dgKappaUnconditionalConeMap_perfect_iff R κ hκ f M).mp hM)

/-- 同値の順射は D-S の元の同じ平坦分解・実商入力射の native nerve そのもの。 -/
theorem dgKappaUnconditionalSuspensionMoritaEquivalence_hom :
    (dgKappaUnconditionalSuspensionMoritaEquivalence R κ hκ f).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
        (perfDGInputHomEquiv R A B f) κ hκ).down := rfl

/-- 元の主導来 Morita 射の、D-S の同じ実懸垂入力射が全 ∞ 圏同値となる。 -/
theorem dgKappaUnconditionalSuspensionInputMap_isQCatEquivalence_of_morita :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.dgKappaSphereClosureSuspensionInputMap R A B
      (perfDGInputHomEquiv R A B f) κ hκ).down) :=
  (dgKappaUnconditionalSuspensionMoritaEquivalence R κ hκ f).isQCatEquivalence

end SerrePositivity.KST.NonConnective
