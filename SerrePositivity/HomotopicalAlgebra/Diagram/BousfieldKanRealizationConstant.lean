module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNerveStandard
public import SerrePositivity.HomotopicalAlgebra.Quillen.Saturation

/-!
概要：BK実現の標準単体による余単体対象はhomotopically constant。
方針：既存の標準単体の収縮をCの通常の局所化に移し、弱同値の検出を使う。
使われ方：HTT 4.2.4.4、RR02(a)の実際のframeの構造射。
規約：SSetのモデル構造は仮定しない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
/-- 標準単体の終対象への射は、実現後に弱同値。 -/
lemma bousfieldKanRealization_terminal_weakEquivalence (n : SimplexCategory) :
    weakEquivalences C ((bousfieldKanParameterRealization K A).map
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n))) := by
  let F := bousfieldKanParameterRealization K A
  let Q := (weakEquivalences C).Q
  have hL : SSet.anodyneExtensions.IsInvertedBy (F ⋙ Q) := by
    intro U V i hi
    exact Localization.inverts Q (weakEquivalences C) _
      (bousfieldKanParameterRealization_map_anodyne K A hA hconst i hi).2
  apply (Quillen.weakEquivalences_iff_isIso_map Q _).mpr
  induction n using SimplexCategory.rec with | _ n =>
  exact SimplicialModel.SimplexNerve.standardTerminal_isIso (F ⋙ Q) hL n

include hA hconst in
/-- 同じ実現による標準単体の構造射は全て弱同値。 -/
lemma bousfieldKanRealization_homotopicallyConstant
    {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C ((SSet.stdSimplex ⋙ bousfieldKanParameterRealization K A).map f) := by
  let F := bousfieldKanParameterRealization K A
  have hn := bousfieldKanRealization_terminal_weakEquivalence K A hA hconst n
  have hm := bousfieldKanRealization_terminal_weakEquivalence K A hA hconst m
  apply (weakEquivalences C).of_postcomp _ _ hm
  have h : SSet.stdSimplex.map f ≫ SSet.stdSimplex.isTerminalObj₀.from _ =
      SSet.stdSimplex.isTerminalObj₀.from _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change weakEquivalences C (F.map (SSet.stdSimplex.map f) ≫ F.map _)
  rw [← F.map_comp, h]
  exact hn

end SerrePositivity.DiagramModel.FrameWeightRealization
