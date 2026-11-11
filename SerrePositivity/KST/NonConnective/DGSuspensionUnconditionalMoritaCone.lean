module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalMapData
public import SerrePositivity.KST.NonConnective.DGKappaConeStrictImagePerfect

/-!
概要：新段提供者の実 cone 射へ、元の導来延長の自然性・Morita 同値性・核反映を代入する。
方針：D-S の同じ strict image を使い、既存の cone・data・実包含を変更しない。
規約：懸垂商の Morita 同値性と反復構造辺の自然性は別工程。c4 の存在は主張しない。
使われ方：K-7 e の新模型上の実 Morita 射と、元の perfect 零化集合の照合。
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
local notation "s" => dgKappaUnconditionalStageProvider R κ hκ

/-- 新提供者の同じ実 cone 射は、元の導来延長と全関手で自然。 -/
def dgKappaUnconditionalConeDerivedSquare :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (dgKappaConeDerivedComparison R A (s A).cone ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleExtensionInfinity R A B (perfDGInputHomEquiv R A B f))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaUnconditionalSuspensionMapData R κ hκ f).cone ≫
        dgKappaConeDerivedComparison R B (s B).cone) :=
  dgKappaConeStrictImageDerivedSquare R A B (perfDGInputHomEquiv R A B f)
    (s A).cone (s B).cone
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R A B (perfDGInputHomEquiv R A B f) hκ Fact.out)

/-- 同じ実主導来 Morita 射の cone 作用は、新提供者上で全 ∞ 圏同値となる。 -/
theorem dgKappaUnconditionalConeMap_isQCatEquivalence_of_morita
    [(dgDerivedExtension R A B (perfDGInputHomEquiv R A B f)).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgKappaUnconditionalSuspensionMapData R κ hκ f).cone) :=
  dgKappaConeStrictImage_isQCatEquivalence_of_morita R A B (perfDGInputHomEquiv R A B f)
    (s A).cone (s B).cone
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R A B (perfDGInputHomEquiv R A B f) hκ Fact.out)

/-- Morita 射の同じ実 cone 作用は、元の商で零化する perfect 集合を保存・反映する。 -/
theorem dgKappaUnconditionalConeMap_perfect_iff
    [(dgDerivedExtension R A B (perfDGInputHomEquiv R A B f)).IsEquivalence]
    (M : DGKappaCone R A (dgKappaUnconditionalStageProvider R κ hκ A).cone) :
    (dgKappaUnconditionalSuspensionMapData R κ hκ f).cone.obj M ∈
        dgKappaConePerfectObjects R B (s B).cone ↔
      M ∈ dgKappaConePerfectObjects R A (s A).cone :=
  dgKappaConeStrictImage_perfect_iff R A B (perfDGInputHomEquiv R A B f)
    (s A).cone (s B).cone
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgKappaSphereClosureExtensionStrictImage R A B (perfDGInputHomEquiv R A B f) hκ Fact.out) M

end SerrePositivity.KST.NonConnective
