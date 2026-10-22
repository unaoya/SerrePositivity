module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalSubcomplexIndexCocone

/-!
概要：元の有限 coslice 図式の展開と添字図式を、同じ小部分複体の指定終頂点へ延ばす。
方針：展開した有限 join の像を含む共通部分複体を取り、同じ終頂点への余錐を作る。
規約：二つの頂点を別々に選ばず、元の指定終頂点と厳密に一致させる。
使われ方：cofinal 性の引き戻しの有限余錐を全鎖の実現空間内で組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ部分複体を添字余錐の頂点とし、その同じ終頂点で元の展開図式を延長できる。 -/
lemma exists_terminalSubcomplex_cosliceCone {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {C : SSet.{u}} [Quasicategory C] [IsKappaFiltered κ C]
    {T : Type u} (hT : κ ≤ Cardinal.mk T) {K : SSet.{u}} [K.Finite]
    (a : K ⟶ nerve (SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T))
      (terminalSubcomplexPredicate _)))
    (p : (Δ[0] : SSet.{u}) ⟶ C ⊗ nerve (Codiscrete T)) (f : K ⟶ sliceUnder p) :
    ∃ (B : SmallSubcomplexFamily κ (C ⊗ nerve (Codiscrete T)) (terminalSubcomplexPredicate _))
      (cI : JoinCocone a) (hB : Subcomplex.range (sliceUnderUncurry f) ≤ B.val),
      cI.vertex = nerveVertex B ∧
      ∃ c : JoinCocone (Subcomplex.lift (sliceUnderUncurry f) hB),
        c.vertex = terminalSubcomplexChosenVertex κ _ B := by
  have : (join (Δ[0] : SSet.{u}) K).Finite := finite_join_of_finite _ _
  obtain ⟨B, cI, hI, hB⟩ := exists_terminalSubcomplex_indexCocone hκ hT a (sliceUnderUncurry f)
  obtain ⟨c, hc⟩ := exists_joinCocone_at_terminal
    (terminalSubcomplexChosenVertex_terminal κ _ B) (Subcomplex.lift (sliceUnderUncurry f) hB)
  exact ⟨B, cI, hB, hI, c, hc⟩

end SerrePositivity.InfinityCategories.F2.Ind
