module
public import SerrePositivity.KST.NonConnective.FixedInput
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableVerdierSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion

/-!
第 I 段延長分の比較目標の型だけを固定する。存在定理・選択による実例は追加しない。
Calkin cone は Indω の κ-compact 部分、商は未完備の Verdier 商とする。
商の存在・Yoneda の因子化・安定性も指定データであり、d4 から推論しない。
逐次比較は Fun(ℕ, Sp) 内の同型であり、段別同型の族ではない。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u})
  (A : PerfDGInput.{u, max (u + 1) v} R)

/-- 比較目標に現れる (Indω ν A)^κ。通常 compact 部分に置き換えない。 -/
abbrev dgKInputCalkinConeTarget :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, max (u + 1) v + 1} κ
    (dgKInputIndCompletion R A)

/-- 同じ Yoneda を含む、未完備 Calkin 商の指定。これの存在は主張しない。 -/
structure DGKInputCalkinPresentation where
  quotient : SSet.{max (u + 1) v + 1}
  [quotientQuasicategory : Quasicategory quotient]
  [quotientStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable quotient]
  [coneStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (dgKInputCalkinConeTarget R κ A)]
  [sourceStable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((SSet.uliftFunctor.{max (u + 1) v + 1,
    max (u + 1) v}).obj (dgKInputStableValue R A).obj)]
  inclusion : (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
    (dgKInputStableValue R A).obj ⟶ dgKInputCalkinConeTarget R κ A
  inclusionYoneda : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (inclusion ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, max (u + 1) v + 1} κ
      (dgKInputIndCompletion R A))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj)
  projection : dgKInputCalkinConeTarget R κ A ⟶ quotient
  verdier : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsStableVerdierSequence inclusion projection

attribute [instance] DGKInputCalkinPresentation.quotientQuasicategory
  DGKInputCalkinPresentation.quotientStable

/-- ν(Σ_dg A) ≃ Idem((Indω ν A)^κ/ν A) の目標型。宇宙上昇を明示する。 -/
abbrev DGNonconnectiveSuspensionComparisonTarget [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (P : DGKInputCalkinPresentation R κ A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    ((SSet.uliftFunctor.{max (u + 1) v + 2, max (u + 1) v}).obj
      (dgKInputStableValue R (dgSuspensionUnconditionalIteration R κ hκ A 1)).obj)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem P.quotient)

/-- D_dg(A) ≃ D_∞(ν A) の目標型。指定 D∞ は延長分から受け取り、存在を主張しない。
FunctorIso は全単体を持つ図式間の可逆二胞体で、構造辺の整合を含む。 -/
abbrev DGNonconnectiveSequenceComparisonTarget [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ)
    (Dinf : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{max (u + 1) v} →
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
        (nerve SequentialIndex.{max (u + 1) v}) ⟶ Sp.{max (u + 1) v})) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgNonconnectiveKFixedInputDiagram R κ hκ A)
    (Dinf (dgKInputStableValue R A))

end SerrePositivity.KST.NonConnective
