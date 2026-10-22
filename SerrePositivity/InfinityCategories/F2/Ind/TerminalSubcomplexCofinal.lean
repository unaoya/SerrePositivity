module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierCofinal
public import SerrePositivity.InfinityCategories.F2.Ind.TrivialSectionCofinal

/-!
概要：保存済みの同じ包含順の nerve から元の底への写像は right cofinal。
方針：同じ実現空間の射影の切断の cofinal 性と、同じ値写像の cofinal 性を合成する。
規約：構成済みの写像を取り替えず、追加の同値性仮定を置かない。
使われ方：κ-filtered な通常の poset への添字の置き換え。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ包含順から元のラベル付き積への、構成済みの同じ実現は right cofinal。 -/
lemma terminalSubcomplexRealization_isRightCofinal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) :
    IsRightCofinal (terminalSubcomplexRealization κ (C ⊗ nerve (Codiscrete T))) := by
  let X := C ⊗ nerve (Codiscrete T)
  let s := terminalCarrierSectionData
    (fun A : SmallSubcomplexFamily κ X (terminalSubcomplexPredicate X) => A.val)
    (fun _ _ h => h) (terminalSubcomplexChosenVertex κ X)
    (terminalSubcomplexChosenVertex_terminal κ X)
  have hs : IsRightCofinal s.val := isRightCofinal_section_of_trivialKanFibration
    (terminalSubcomplexCarrierProjection κ X) s.val s.property
  change IsRightCofinal (s.val ≫ terminalSubcomplexCarrierValue κ X)
  exact hs.comp (terminalSubcomplexCarrierValue_isRightCofinal hκ hT)

/-- 保存済みの同じ元の底への写像は right cofinal。 -/
lemma terminalSubcomplexBaseMap_isRightCofinal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) : IsRightCofinal (terminalSubcomplexBaseMap κ C T) := by
  have := nonempty_labels_of_regular_bound hκ hT
  exact (terminalSubcomplexRealization_isRightCofinal hκ hT).comp
    (codiscreteProductProjection_isRightCofinal C T)

end SerrePositivity.InfinityCategories.F2.Ind
