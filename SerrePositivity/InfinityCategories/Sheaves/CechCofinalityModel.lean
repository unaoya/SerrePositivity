module

public import SerrePositivity.InfinityCategories.Sheaves.CechCommaSmallContraction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CommaComparisons.AsSmallComma
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.NerveLeftQuillenA
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.QCatEquivalence

/-!
概要：弱終対象の指定 Čech 図式は、共通の小さい模型で left cofinal。
方針：既存の comma の宇宙比較で構成済みの収縮を移し、Quillen A を用いる。
  文献対応：HTT 4.1.3.1、Kerodon Theorem 7.2.3.1（Tag 02NY）。
規約：元の弱終性のみを使う。cofinality は入力にしない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.AsSmallComma
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [Category.{v} C] {U : C}

/-- 元の Čech 図式を対象・射の共通の小さい模型で読む。 -/
def cechSmallFunctor (d : CategoryTheory.CechNerveData U) :
    AsSmall.{max u v w} SimplexCategory ⥤ AsSmall.{w} Cᵒᵖ :=
  smallFunctor.{0, 0, u, v, w} d.obj.rightOp

/-- 指定 Čech 図式の小さい模型は弱終性から left cofinal。 -/
lemma cechSmallFunctor_nerve_isLeftCofinal (d : CategoryTheory.CechNerveData U)
    (hU : CategoryTheory.IsWeaklyTerminal U) :
    IsLeftCofinal (nerveMap (cechSmallFunctor.{u, v, w} d)) := by
  apply nerveMap_isLeftCofinal_of_weaklyContractible_comma
  intro q
  let V : C := (AsSmall.down.obj q).unop
  obtain ⟨r⟩ := hU V
  let e := equivalence.{0, 0, u, v, w} d.obj.rightOp (Opposite.op V)
  have hc := cechCommaSmall_isWeaklyContractible.{u, v, w} d r
  exact (nerveQCatEquivalence e).isQCatEquivalence.isWeakHomotopyEquivalence
    |>.weaklyContractible_iff.mpr hc

end SerrePositivity.InfinityCategories.Sheaves
