module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTransformationCylinder
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightReindexingDinaturality
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexing
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization

/-!
概要：指定添字自然変換の円柱の実現の両端を、元の添字変更射に同定する。
方針：円柱の端点式、添字変更のdinaturality、係数移送の自然性を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の余単位による実現比較。
規約：両端は元の実射そのもの。局所化での同定は別に行う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {P Q : L ⥤ K} (α : P ⟶ Q) (A : K ⥤ SimplexCategory ⥤ C)

/-- 重みの円柱を実現して、元の添字変更を続ける。 -/
def bousfieldKanTransformationRealization :
    (bousfieldKanParameterRealization L (P ⋙ A)).obj (Δ[1] : SSet.{w}) ⟶
      (functor K A).obj (bousfieldKanWeight Kᵒᵖ) :=
  (functor L (P ⋙ A)).map (bousfieldKanTransformationCylinder α) ≫
    reindexMap P A (bousfieldKanWeight Kᵒᵖ)

lemma bousfieldKanTransformationRealization_zero :
    (functor L (P ⋙ A)).map (terminalWeightEndpoint (K := L) 0) ≫
        bousfieldKanTransformationRealization α A =
      (map L (Functor.whiskerRight α A)).app (bousfieldKanWeight Lᵒᵖ) ≫
        bousfieldKanReindexMap Q A := by
  unfold bousfieldKanTransformationRealization
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    bousfieldKanTransformationCylinder_zero, CategoryTheory.Functor.map_comp,
    Category.assoc, reindexMap_dinaturality, ← Category.assoc,
    (map L (Functor.whiskerRight α A)).naturality]
  exact Category.assoc _ _ _

lemma bousfieldKanTransformationRealization_one :
    (functor L (P ⋙ A)).map (terminalWeightEndpoint (K := L) 1) ≫
        bousfieldKanTransformationRealization α A = bousfieldKanReindexMap P A := by
  unfold bousfieldKanTransformationRealization
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    bousfieldKanTransformationCylinder_one]
  rfl

end SerrePositivity.DiagramModel.FrameWeightRealization
