module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTerminalWeightLocalization
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationConstant

/-!
概要：終対象のある添字で、零重みへの指定射のframe実現は弱同値。
方針：既存の標準単体の収縮を用い、重みの収縮を通常の局所化へ送る。
使われ方：HTT 4.2.4.4、RR02(a)の元の増大射の値ごとの比較。
規約：SSetのモデル構造を仮定せず、指定された零重み射を用いる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]

lemma terminalWeightProjection_eq :
    terminalWeightProjection (K := K) =
      (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).map
          (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj (SimplexCategory.mk 1))) ≫
        (bousfieldKanZeroParameterIso K).hom := by
  apply NatTrans.ext
  funext k
  rfl

variable {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
lemma terminalWeightProjection_realization_weakEquivalence :
    weakEquivalences C ((functor K A).map (terminalWeightProjection (K := K))) := by
  rw [terminalWeightProjection_eq, Functor.map_comp]
  apply (weakEquivalences C).comp_mem
  · exact bousfieldKanRealization_terminal_weakEquivalence K A hA hconst _
  · exact (weakEquivalences C).of_isIso _

include hA hconst in
/-- 終対象による重みの収縮を実現し、指定零重み射の弱同値性を得る。 -/
lemma bousfieldKanZeroWeight_realization_weakEquivalence {t : K} (ht : IsTerminal t) :
    weakEquivalences C ((functor K A).map (bousfieldKanZeroWeight K)) := by
  let Q := (weakEquivalences C).Q
  let F := functor K A ⋙ Q
  letI : IsIso (F.map (terminalWeightProjection (K := K))) :=
    Localization.inverts Q (weakEquivalences C) _
      (terminalWeightProjection_realization_weakEquivalence K A hA hconst)
  apply (Quillen.weakEquivalences_iff_isIso_map Q _).mpr
  exact (terminalZeroWeightMapIso F ht).isIso_hom

end SerrePositivity.DiagramModel.FrameWeightRealization
