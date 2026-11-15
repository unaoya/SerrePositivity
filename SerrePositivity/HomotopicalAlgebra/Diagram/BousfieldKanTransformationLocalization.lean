module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTransformationRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTerminalRealization

/-!
概要：指定添字自然変換で結ばれる実現比較は通常の局所化で一致する。
方針：元の円柱射影の弱同値性で両端を同定し、実射の端点式を使う。
使われ方：HTT 4.2.4.4、RR02(a)の随伴の余単位による比較。
規約：同じ元の比較射を局所化へ送り、SSetのモデル構造を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  {P Q : L ⥤ K} (α : P ⟶ Q) (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ l, reedyLeft simplex (cofibrations C) (initial.to ((P ⋙ A).obj l)))
  (hconst : ∀ l, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C (((P ⋙ A).obj l).map f))

include hA hconst in
/-- 係数移送を含めた二つの元の添字変更は、同じ局所化の射となる。 -/
lemma bousfieldKanReindexMap_localization_naturality :
    (weakEquivalences C).Q.map (bousfieldKanReindexMap P A) =
      (weakEquivalences C).Q.map
        ((map L (Functor.whiskerRight α A)).app (bousfieldKanWeight Lᵒᵖ) ≫
          bousfieldKanReindexMap Q A) := by
  let R := (weakEquivalences C).Q
  let F := functor L (P ⋙ A) ⋙ R
  letI : IsIso (F.map (terminalWeightProjection (K := L))) :=
    Localization.inverts R (weakEquivalences C) _
      (terminalWeightProjection_realization_weakEquivalence L (P ⋙ A) hA hconst)
  rw [← bousfieldKanTransformationRealization_one α A,
    ← bousfieldKanTransformationRealization_zero α A,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  exact congrArg (fun f => f ≫ R.map (bousfieldKanTransformationRealization α A))
    (terminalWeightEndpoint_map_eq F).symm

end SerrePositivity.DiagramModel.FrameWeightRealization
