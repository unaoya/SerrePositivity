module

public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedContractibility
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence

/-!
概要：sifted 添字上の一点図式の全空間 Kan 模型は、終対象と同値。
方針：元の添字の弱可縮性を、元の Kan 置換の単位の弱同値性で移す。
規約：元の添字に充填性を仮定しない。使われ方：有限積の交換の空積の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- sifted 添字の全空間 Kan 模型から一点への元の射は弱ホモトピー同値。 -/
lemma continuousKanTerminalComparison_isWeakHomotopyEquivalence_of_sifted
    (K : SSet.{u}) [IsSiftedInfinity K] :
    IsWeakHomotopyEquivalence (terminal.from (F2.continuousKanReplacement.obj K)) := by
  apply (F2.continuousKanReplacementUnit_isWeakHomotopyEquivalence K).cancel_left
  have he : F2.continuousKanReplacementUnit.app K ≫
      terminal.from (F2.continuousKanReplacement.obj K) = terminal.from K :=
    terminal.hom_ext _ _
  rw [he]
  exact isWeaklyContractible_of_sifted K

/-- sifted 添字の元の全空間 Kan 模型は、全境界を充填する可縮 Kan 複体。 -/
lemma continuousKanReplacement_isContractibleKan_of_sifted
    (K : SSet.{u}) [IsSiftedInfinity K] :
    IsContractibleKan (F2.continuousKanReplacement.obj K) := by
  have := isContractibleKan_terminal.{u}.kanComplex
  have h := continuousKanTerminalComparison_isWeakHomotopyEquivalence_of_sifted K
  exact h.isSimplicialHomotopyEquivalence.isContractibleKan_iff.mpr isContractibleKan_terminal

end SerrePositivity.InfinityCategories.HomotopyLimits
