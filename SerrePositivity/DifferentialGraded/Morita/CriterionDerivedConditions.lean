module
public import SerrePositivity.DifferentialGraded.Morita.CriterionDerivedEquivalence
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfConditions
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerf

/-! # Perf判定の十分性を明示した入力とする全導来Morita拡張

他担当の三条件そのものを用いる。従来の十分性を入力するAPIを保ち、
完成したPerf判定でその入力を供給する版も公開する。
-/
@[expose] public section
noncomputable section
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]

/-- 三条件から実際のPerf同値の証拠を得る十分性定理の型。
従来の条件付きAPIの入力型を保持する。成立は後の補題で証明する。 -/
def CriterionDerivedPerfSufficiency : Prop :=
  ∀ K : Kernel A D E, CriterionPerfConditions A D E K →
    Nonempty (CriterionPerfEquivalenceWitness A D E K)

/-- Perf十分性定理を入力として、元の三条件とcompact生成から主作用の同値性を得る。 -/
lemma criterionDerivedKernelIsEquivalenceOfConditions
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence := by
  obtain ⟨W⟩ := hPerf K hK
  have := W.actionIsEquivalence A D E K
  exact criterionDerivedKernelIsEquivalence A D E K (W.columnsPerfect A D E K) G hG H hH

/-- 三条件を元の型のまま受け取る、明示的に条件付きの全主導来圏Morita同値。 -/
def criterionDerivedKernelEquivalenceOfConditions
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E := by
  have := criterionDerivedKernelIsEquivalenceOfConditions A D E hPerf K hK G hG H hH
  exact (kernelDerivedTensor A D E K).asEquivalence

lemma criterionDerivedKernelEquivalenceOfConditions_functor
    (hPerf : CriterionDerivedPerfSufficiency A D E)
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfConditions A D E hPerf K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

/-- 完成した一般kernelのPerf判定は、従来の十分性入力を供給する。 -/
lemma criterionDerivedPerfSufficiency : CriterionDerivedPerfSufficiency A D E :=
  fun K hK => ⟨criterionPerfEquivalenceOfConditions A D E K hK⟩

/-- 三条件と両側のcompact生成から、実際の主導来kernel作用は同値である。 -/
lemma criterionDerivedKernelIsEquivalenceOfMoritaConditions
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (kernelDerivedTensor A D E K).IsEquivalence :=
  criterionDerivedKernelIsEquivalenceOfConditions A D E
    (criterionDerivedPerfSufficiency A D E) K hK G hG H hH

/-- Perf十分性の追加入力を要しない、三条件による全主導来圏Morita同値。 -/
def criterionDerivedKernelEquivalenceOfMoritaConditions
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    DerivedModuleCategory A D ≌ DerivedModuleCategory A E :=
  criterionDerivedKernelEquivalenceOfConditions A D E
    (criterionDerivedPerfSufficiency A D E) K hK G hG H hH

/-- 構成した同値の順方向は、既存の主導来tensor作用そのものである。 -/
lemma criterionDerivedKernelEquivalenceOfMoritaConditions_functor
    (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
    {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
    (hG : CriterionDerivedCompactGeneration A D G)
    {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
    (hH : CriterionDerivedCompactGeneration A E H) :
    (criterionDerivedKernelEquivalenceOfMoritaConditions A D E K hK G hG H hH).functor =
      kernelDerivedTensor A D E K := rfl

end SerrePositivity.DifferentialGraded.Morita
