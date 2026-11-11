module
public import SerrePositivity.KST.Fibration.RelativeSQuotient
public import SerrePositivity.KST.Fibration.KernelWeakContractibility

/-! # 核の全 gapped S 図式の相対条件と弱可縮性

実 Verdier 列の包含を通る図式は商で全成分が零になる。
従って相対条件は全 S_n(D) を保持し、その零対象から各段の弱可縮性を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 包含を通る全 S_n 図式で相対条件は自動的に成立する。 -/
lemma relativeSKernel_eq_top
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    relativeSConstruction (i.hom ≫ q.hom) n = ⊤ :=
  relativeDiagram_eq_top_of_zero (i.hom ≫ q.hom) (sComponentEvaluation A.obj n)
    (fun a x => h.kills_inclusion ((sComponentEvaluation A.obj n a).app _ x))

/-- 包含を通る相対 S_n の全単体集合は、元の零図式によって弱可縮。 -/
lemma relativeSKernel_isWeaklyContractible
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (relativeSConstruction (i.hom ≫ q.hom) n : SSet.{u}) :=
  relativeDiagram_kernel_isWeaklyContractible h
    (fun a : (arNerve n) _⦋0⦌ => sComponentEvaluation A.obj n a ≫ i.hom)
    (fun a x => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.image_mem_essentialImage i ((sComponentEvaluation A.obj n a).app _ x))

end SerrePositivity.KST.Fibration
