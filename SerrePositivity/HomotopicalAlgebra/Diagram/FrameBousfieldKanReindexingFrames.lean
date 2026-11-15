module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexing
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
概要：指定添字変更射はframe族の射と両立する。
方針：実現随伴で転置し、元の係数移送の自然性を使う。
使われ方：HTT 4.2.4.4、RR02(a)の随伴の単位・余単位の実現。
規約：指定した添字変更とframe実現の射を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (P : L ⥤ K) {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B)

lemma reindexMap_frame_naturality (W : Kᵒᵖ ⥤ SSet.{w}) :
    reindexMap P A W ≫ (map K a).app W =
      (map L (Functor.whiskerLeft P a)).app (P.op ⋙ W) ≫ reindexMap P B W := by
  have h : (adjunction K A).homEquiv W _ ((map K a).app W) =
      (adjunction K B).unit.app W ≫ ((homFamily K).map a.op).app _ := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      homEquiv_frame_naturality K a W ((functor K B).obj W) (𝟙 _)
  apply ((adjunction L (P ⋙ A)).homEquiv _ _).injective
  rw [reindexMap_homEquiv_comp, h, homEquiv_frame_naturality, reindexMap_homEquiv]
  apply NatTrans.ext
  funext e
  simp [homReindexIso]

lemma bousfieldKanReindexMap_frame_naturality :
    bousfieldKanReindexMap P A ≫ (map K a).app (bousfieldKanWeight Kᵒᵖ) =
      (map L (Functor.whiskerLeft P a)).app (bousfieldKanWeight Lᵒᵖ) ≫
        bousfieldKanReindexMap P B := by
  unfold bousfieldKanReindexMap
  rw [Category.assoc, reindexMap_frame_naturality, ← Category.assoc,
    (map L (Functor.whiskerLeft P a)).naturality, Category.assoc]

end SerrePositivity.DiagramModel.FrameWeightRealization
