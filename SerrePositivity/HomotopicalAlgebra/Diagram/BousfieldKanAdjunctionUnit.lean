module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexingFrames
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexingComposition
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanTransformationLocalization

/-!
概要：随伴の単位から、指定BK添字変更の局所化での逆の候補を作る。
方針：単位を係数へ作用させて左随伴の添字変更を続け、単位の円柱で合成を照合する。
使われ方：HTT 4.2.4.4、RR02(a)の要素圏とOverの随伴。
規約：元の指定単位と指定添字変更を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  {S : K ⥤ L} {P : L ⥤ K} (adj : S ⊣ P) (A : K ⥤ SimplexCategory ⥤ C)

/-- 指定単位の係数移送の後に左随伴の指定添字変更を合成する。 -/
def adjointReindexInverse :
    (functor K A).obj (bousfieldKanWeight Kᵒᵖ) ⟶
      (functor L (P ⋙ A)).obj (bousfieldKanWeight Lᵒᵖ) :=
  (map K (Functor.whiskerRight adj.unit A)).app (bousfieldKanWeight Kᵒᵖ) ≫
    bousfieldKanReindexMap S (P ⋙ A)

/-- 元の右三角恒等式を係数frameへ移す。 -/
lemma adjointReindex_coefficient_triangle :
    Functor.whiskerLeft P (Functor.whiskerRight adj.unit A) ≫
      Functor.whiskerRight adj.counit (P ⋙ A) = 𝟙 (P ⋙ A) := by
  apply NatTrans.ext
  funext l
  change A.map (adj.unit.app (P.obj l)) ≫ A.map (P.map (adj.counit.app l)) = 𝟙 _
  rw [← A.map_comp, adj.right_triangle_components]
  exact A.map_id _

variable [ModelCategory C]
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include hA hconst in
lemma adjointReindexInverse_comp_localization :
    (weakEquivalences C).Q.map
      (adjointReindexInverse adj A ≫ bousfieldKanReindexMap P A) = 𝟙 _ := by
  have h := bousfieldKanReindexMap_localization_naturality adj.unit A hA hconst
  rw [bousfieldKanReindexMap_id, CategoryTheory.Functor.map_id] at h
  unfold adjointReindexInverse
  rw [Category.assoc, bousfieldKanReindexMap_comp]
  exact h.symm

end SerrePositivity.DiagramModel.FrameWeightRealization
