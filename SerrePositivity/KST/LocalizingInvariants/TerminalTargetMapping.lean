module

public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：終対象を終点とする写像空間の間の元の関手による射は同値。
方針：両写像空間の可縮 Kan 性と点への全境界充填から二対三則で導く。
規約：元の関手の fibration 性を仮定しない。使われ方：Tamme の引き戻しの C 辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma mapOfContractibleKan_equivalence {K L : SSet.{u}} (f : K ⟶ L)
    (hK : IsContractibleKan K) (hL : IsContractibleKan L) :
    IsSimplicialHomotopyEquivalence f := by
  have hT : IsContractibleKan (⊤_ SSet.{u}) :=
    fun n b => ⟨terminal.from _, terminal.hom_ext _ _⟩
  have := hT.kanComplex
  have := hK.kanComplex
  have := hL.kanComplex
  have := (isContractibleKan_iff_trivialKanFibration K).mp hK
  have := (isContractibleKan_iff_trivialKanFibration L).mp hL
  have h : IsQCatEquivalence (f ≫ terminal.from L) := by
    rw [show f ≫ terminal.from L = terminal.from K from terminal.hom_ext _ _]
    exact isQCatEquivalence_of_trivialKanFibration _
  exact ((isQCatEquivalence_of_trivialKanFibration (terminal.from L)).cancel_right h
    ).isSimplicialHomotopyEquivalence

lemma terminalTargetPinchedHomMap_equivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (x z : X _⦋0⦌)
    (hz : IsTerminalVertex z) (hFz : IsTerminalVertex (F.app (Opposite.op ⦋0⦌) z)) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap F x z) :=
  mapOfContractibleKan_equivalence _ (hz.pinchedHom_isContractibleKan x)
    (hFz.pinchedHom_isContractibleKan _)

end SerrePositivity.KST.LocalizingInvariants
