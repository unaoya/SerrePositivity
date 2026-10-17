module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfGeneration

/-! # 実際の kernel 作用が Perf 上の同値であることの証拠

同値（逆関手と二つの自然同型を含む）と、主導来作用との比較を保持する。
一般 kernel の右随伴は構成しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 任意の圏同値ではなく、実際の主作用に一致する Perf 同値の証拠。 -/
structure CriterionPerfEquivalenceWitness where
  equivalence : PerfectModuleCategory A D ≌ PerfectModuleCategory A E
  comparison : perfectModuleInclusion A D Set.univ ⋙ kernelDerivedTensor A D E K ≅
    equivalence.functor ⋙ perfectModuleInclusion A E Set.univ

variable (W : CriterionPerfEquivalenceWitness A D E K)
include W

/-- 同値との比較だけで、列の perfect 性が必要になる。 -/
lemma CriterionPerfEquivalenceWitness.columnsPerfect : kernelColumnsPerfect A D E K := by
  apply (kernelColumnsPerfect_iff_preservesPerfect A D E K).2
  intro X hX
  exact (modulePerfect A E).prop_of_iso (W.comparison.app ⟨X, hX⟩).symm
    (W.equivalence.functor.obj ⟨X, hX⟩).property

local instance : (perfectModuleInclusion A E Set.univ).Full :=
  inferInstanceAs ((modulePerfect A E).ι.Full)
local instance : (perfectModuleInclusion A E Set.univ).Faithful :=
  inferInstanceAs ((modulePerfect A E).ι.Faithful)

/-- 列の perfect 性から得た実際の制限と、証拠に含まれる同値との自然同型。 -/
def CriterionPerfEquivalenceWitness.actionIso :
    perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K) ≅ W.equivalence.functor :=
  Functor.fullyFaithfulCancelRight (perfectModuleInclusion A E Set.univ)
    (perfectDerivedKernelActionInclusionIso A D E K _ ≪≫ W.comparison)

/-- 実際の制限も圏同値である。 -/
lemma CriterionPerfEquivalenceWitness.actionIsEquivalence :
    (perfectDerivedKernelAction A D E K (W.columnsPerfect A D E K)).IsEquivalence :=
  Functor.isEquivalence_of_iso (W.actionIso A D E K).symm

/-- 同値の必要条件としての厚い生成性。 -/
lemma CriterionPerfEquivalenceWitness.columnsThickGenerate :
    criterionPerfColumnsThickGenerate A D E K := by
  let := W.actionIsEquivalence A D E K
  exact criterionPerf_columnsThickGenerate_of_essSurj A D E K (W.columnsPerfect A D E K)

omit W in
/-- 充満忠実性と厚い生成性が揃った実際の制限から、同値の証拠を取り出す。 -/
def criterionPerfEquivalenceWitnessOfFullyFaithful
    (hK : kernelColumnsPerfect A D E K)
    [(perfectDerivedKernelAction A D E K hK).Full]
    [(perfectDerivedKernelAction A D E K hK).Faithful]
    (hgen : criterionPerfColumnsThickGenerate A D E K) :
    CriterionPerfEquivalenceWitness A D E K := by
  let := criterionPerf_essSurj_of_columnsThickGenerate A D E K hK hgen
  let : (perfectDerivedKernelAction A D E K hK).IsEquivalence := {}
  exact ⟨(perfectDerivedKernelAction A D E K hK).asEquivalence,
    (perfectDerivedKernelActionInclusionIso A D E K hK).symm⟩

end SerrePositivity.DifferentialGraded.Morita
