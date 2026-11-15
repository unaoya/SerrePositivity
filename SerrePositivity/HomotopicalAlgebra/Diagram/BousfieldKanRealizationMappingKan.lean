module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SectionsKan

/-!
概要：BKパラメータ付き実現の右随伴は、fibrantな標的でKan値を取る。
方針：各frameのhorn tensorの既存の判定と、BK endのKan性を合成する。
使われ方：HTT 4.2.4.4、RR02(a)の同じ実現随伴の写像空間。
規約：SSetのモデル構造を仮定せず、図式の遷移にfibration性を課さない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
/-- 同じ実現随伴の右辺は、fibrantな標的でKan複体となる。 -/
lemma bousfieldKanParameterHom_kanComplex (Y : C) [IsFibrant Y] :
    SSet.KanComplex
      ((hom K A ⋙ weightedSectionsFunctor (bousfieldKanWeight Kᵒᵖ)).obj Y) := by
  have : ∀ k, SSet.KanComplex (((hom K A).obj Y).obj k) := by
    intro k
    exact HomotopyFunctionComplex.cosimplicialHom_kanComplex
      (A.obj k.unop) (hA k.unop) (hconst k.unop) Y
  exact bousfieldKanHolim_kanComplex ((hom K A).obj Y)

end SerrePositivity.DiagramModel.FrameWeightRealization
