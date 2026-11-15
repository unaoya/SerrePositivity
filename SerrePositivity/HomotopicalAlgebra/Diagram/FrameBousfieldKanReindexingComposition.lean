module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanReindexing

/-!
概要：指定frame実現の添字変更射の単位則と合成則。
方針：実現随伴の転置で照合し、BK重みの既存の合成則を適用する。
使われ方：HTT 4.2.4.4、RR02(a)の要素圏とOverの随伴の移送。
規約：指定された添字変更射を使い、弱同値性はここでは主張しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L M : Type w} [SmallCategory K] [SmallCategory L] [SmallCategory M]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

lemma reindexMap_id (A : K ⥤ SimplexCategory ⥤ C) (W : Kᵒᵖ ⥤ SSet.{w}) :
    reindexMap (𝟭 K) A W = 𝟙 _ := by
  have hop : (𝟭 K).op = 𝟭 Kᵒᵖ := rfl
  have h := reindexMap_homEquiv (𝟭 K) A W
  simp only [hop, CategoryTheory.Functor.id_comp] at h
  apply ((adjunction K A).homEquiv _ _).injective
  rw [h]
  change Functor.whiskerLeft (𝟭 Kᵒᵖ) ((adjunction K A).unit.app W) ≫ 𝟙 _ = _
  simp only [Category.comp_id]
  exact ((adjunction K A).homEquiv_id _).symm

lemma reindexMap_comp (P : L ⥤ K) (Q : M ⥤ L)
    (A : K ⥤ SimplexCategory ⥤ C) (W : Kᵒᵖ ⥤ SSet.{w}) :
    reindexMap Q (P ⋙ A) (P.op ⋙ W) ≫ reindexMap P A W =
      reindexMap (Q ⋙ P) A W := by
  have h₁ := reindexMap_homEquiv_comp Q (P ⋙ A) (P.op ⋙ W)
    ((functor K A).obj W) (reindexMap P A W)
  rw [reindexMap_homEquiv] at h₁
  have h₂ := reindexMap_homEquiv (Q ⋙ P) A W
  simp only [CategoryTheory.Functor.assoc] at h₂
  change ((adjunction M (Q ⋙ P ⋙ A)).homEquiv (Q.op ⋙ P.op ⋙ W)
    ((functor K A).obj W)) (reindexMap (Q ⋙ P) A W) = _ at h₂
  apply ((adjunction M (Q ⋙ P ⋙ A)).homEquiv _ _).injective
  rw [h₁, h₂]
  change Functor.whiskerLeft Q.op
      (Functor.whiskerLeft P.op ((adjunction K A).unit.app W) ≫ 𝟙 _) ≫ 𝟙 _ =
    Functor.whiskerLeft (Q ⋙ P).op ((adjunction K A).unit.app W) ≫ 𝟙 _
  simp only [Category.comp_id]
  rfl

lemma bousfieldKanReindexMap_id (A : K ⥤ SimplexCategory ⥤ C) :
    bousfieldKanReindexMap (𝟭 K) A = 𝟙 _ := by
  change (functor K A).map (bousfieldKanWeightPost (𝟭 Kᵒᵖ)) ≫
    reindexMap (𝟭 K) A _ = 𝟙 _
  rw [bousfieldKanWeightPost_id, CategoryTheory.Functor.map_id, reindexMap_id, Category.id_comp]
  rfl

lemma bousfieldKanReindexMap_comp (P : L ⥤ K) (Q : M ⥤ L)
    (A : K ⥤ SimplexCategory ⥤ C) :
    bousfieldKanReindexMap Q (P ⋙ A) ≫ bousfieldKanReindexMap P A =
      bousfieldKanReindexMap (Q ⋙ P) A := by
  dsimp only [bousfieldKanReindexMap]
  rw [Category.assoc, ← Category.assoc (reindexMap Q (P ⋙ A) _) _ _,
    ← reindexMap_naturality Q (P ⋙ A), Category.assoc,
    reindexMap_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
  congr 1


end SerrePositivity.DiagramModel.FrameWeightRealization
