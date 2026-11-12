module
public import SerrePositivity.KST.SConstruction.AssemblyFactorArrowDiagrams
public import SerrePositivity.KST.SConstruction.ContractibleWeightedDiagramLifting

/-! # 全入力射列に沿う両因子の coherent な選択空間
概要：小さい入力図式の全ての射にわたる延長・逆射の compatible な選択を作る。
方針：両側合成の厳密な図式に Bousfield–Kan end と weighted nerve の相対充填を適用する。
規約：整合性は over 圏の nerve 全体で持ち、指定した部分図式を厳密に保持する。
使われ方：構造射の全入力射列の整合性を、単一の辺や二入力の存在から分離して供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 全入力射列にわたる混合 Kan 延長の coherent な全選択。 -/
def kanAssemblyCoherentChoices {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (kanAssemblyInputArrowDiagram r F)

/-- 全入力射列にわたる混合比較逆射の coherent な全選択。 -/
def oneDirectionInverseCoherentChoices {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (oneDirectionInverseInputArrowDiagram r F)

/-- 全入力射列の延長選択は可縮 Kan であり、特に存在する。 -/
lemma kanAssemblyCoherentChoices_isContractibleKan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (kanAssemblyCoherentChoices r F) :=
  contractibleDiagramSelections_isContractibleKan _
    (kanAssemblyInputArrowDiagram_isContractibleKan r F)

/-- 全入力射列の逆射選択は可縮 Kan であり、特に存在する。 -/
lemma oneDirectionInverseCoherentChoices_isContractibleKan {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (oneDirectionInverseCoherentChoices r F) :=
  contractibleDiagramSelections_isContractibleKan _
    (oneDirectionInverseInputArrowDiagram_isContractibleKan r F)

/-- 延長の全選択の各点は、各入力射の over 圏の nerve 上の厳密に自然な族を与える。 -/
def kanAssemblyCoherentFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (kanAssemblyCoherentChoices r F) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AssemblyInputArrow I) ⟶ kanAssemblyInputArrowDiagram r F :=
  diagramSelectionAt _ v

/-- 逆射の全選択の各点は、各入力射の over 圏の nerve 上の厳密に自然な族を与える。 -/
def oneDirectionInverseCoherentFamily {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) (v : (oneDirectionInverseCoherentChoices r F) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AssemblyInputArrow I) ⟶ oneDirectionInverseInputArrowDiagram r F :=
  diagramSelectionAt _ v

/-- 延長の coherent な全選択の族は、任意単射の既存部分を保って補完できる。 -/
lemma kanAssemblyCoherentChoices_relative_lifting {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {S T : SSet.{u}}
    (j : S ⟶ T) [Mono j] (a : S ⟶ kanAssemblyCoherentChoices r F) :
    ∃ b : T ⟶ kanAssemblyCoherentChoices r F, j ≫ b = a :=
  contractibleDiagramSelections_relative_lifting _
    (kanAssemblyInputArrowDiagram_isContractibleKan r F) j a

/-- 逆射の coherent な全選択の族は、任意単射の既存部分を保って補完できる。 -/
lemma oneDirectionInverseCoherentChoices_relative_lifting {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {S T : SSet.{u}}
    (j : S ⟶ T) [Mono j] (a : S ⟶ oneDirectionInverseCoherentChoices r F) :
    ∃ b : T ⟶ oneDirectionInverseCoherentChoices r F, j ≫ b = a :=
  contractibleDiagramSelections_relative_lifting _
    (oneDirectionInverseInputArrowDiagram_isContractibleKan r F) j a

/-- 底の部分図式で指定した延長の coherent な選択を、全射図式の上へ厳密に延長できる。 -/
lemma kanAssemblyCoherentSection_extension {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {A : SSet.{u}}
    (j : A ⟶ nerve (AssemblyInputArrow I)) [Mono j]
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (kanAssemblyInputArrowDiagram r F))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (kanAssemblyInputArrowDiagram r F) = j) :
    ∃ s : nerve (AssemblyInputArrow I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (kanAssemblyInputArrowDiagram r F),
      j ≫ s = a ∧ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (kanAssemblyInputArrowDiagram r F) = 𝟙 _ :=
  contractibleWeightedDiagram_section_extension _
    (kanAssemblyInputArrowDiagram_isContractibleKan r F) j a h

/-- 底の部分図式で指定した逆射の coherent な選択を、全射図式の上へ厳密に延長できる。 -/
lemma oneDirectionInverseCoherentSection_extension {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {A : SSet.{u}}
    (j : A ⟶ nerve (AssemblyInputArrow I)) [Mono j]
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (oneDirectionInverseInputArrowDiagram r F))
    (h : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (oneDirectionInverseInputArrowDiagram r F) = j) :
    ∃ s : nerve (AssemblyInputArrow I) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (oneDirectionInverseInputArrowDiagram r F),
      j ≫ s = a ∧ s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (oneDirectionInverseInputArrowDiagram r F) = 𝟙 _ :=
  contractibleWeightedDiagram_section_extension _
    (oneDirectionInverseInputArrowDiagram_isContractibleKan r F) j a h

end SerrePositivity.KST.SConstruction
