module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFreeArrowAugmentationHomWeak
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameArrowComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanAugmentationConeHom
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanDoubleOpposite

/-!
概要：元の自由増大射のHomをBK表示し、指定したframe arrow錐比較と同定する。
方針：余錐のHomの脚を既存の自由図式随伴で照合し、錐比較の自然性を使う。
使われ方：HTT 4.2.4.4、RR02(a)の指定比較射の同定。
規約：元のstrictDiagramFrameArrowComparisonを保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.DiagramModel
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
local instance : ModelCategory (StrictComplexDiagram A d) := strictDiagramReedyModelCategory A d
local instance : HasColimitsOfSize.{u, u} (Complex A) :=
  ⟨fun _ _ => HomologicalComplex.instHasColimitsOfShape⟩
local instance : ∀ (i j : strictDiagramIndex d),
    HasCoproductsOfShape (i ⟶ j) (Complex A) :=
  fun _ _ => HomologicalComplex.instHasColimitsOfShape

/-- 二つの指定Hom同型を通した前合成は、元のframe arrow比較射と一致する。 -/
lemma strictDiagramFreeArrowConeHom_eq (X Y : StrictComplexDiagram A d) :
    (cosimplicialHomMap (strictDiagramFreeArrowRealizedAugmentation A d X)).app
        (strictDiagramFibrantTarget A d Y) ≫
      (FrameWeightRealization.bousfieldKanRealizationHomIso (StrictDiagramArrowElements.{u} d)ᵒᵖ
        (strictDiagramFreeArrowFrame A d X)).hom.app (strictDiagramFibrantTarget A d Y) ≫
      (bousfieldKanOpOpIso (StrictDiagramArrowElements.{u} d)
        ((FrameWeightRealization.hom (StrictDiagramArrowElements.{u} d)ᵒᵖ
          (strictDiagramFreeArrowFrame A d X)).obj (strictDiagramFibrantTarget A d Y))).hom ≫
      (weightedSectionsFunctor (bousfieldKanWeight (StrictDiagramArrowElements.{u} d))).map
        (strictDiagramFreeArrowHomNatIso A d X Y).hom =
      strictDiagramFrameArrowComparison A d X Y := by
  let c := (Cone.postcompose (strictDiagramFreeArrowHomNatIso A d X Y).inv).obj
    (strictDiagramFrameArrowCone A d X Y)
  have hc : ∀ k, c.π.app k =
      (cosimplicialHomMap ((strictDiagramFreeArrowAugmentation A d X).app (Opposite.op k))).app
        (strictDiagramFibrantTarget A d Y) := by
    intro k
    apply (cancel_mono (strictDiagramFreeArrowHomIso A d X Y k).hom).mp
    change (_ ≫ (strictDiagramFreeArrowHomIso A d X Y k).inv) ≫ _ = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (strictDiagramFreeArrowAugmentation_hom A d X Y k).symm
  have h := FrameWeightRealization.bousfieldKanAugmentationHom_cone
    (StrictDiagramArrowElements.{u} d)ᵒᵖ (strictDiagramFreeArrowFrame A d X)
    (strictDiagramSourceFrame A d X).obj (strictDiagramFreeArrowAugmentation A d X)
    (strictDiagramFibrantTarget A d Y)
    (c.whisker (unopUnop (StrictDiagramArrowElements.{u} d))).π
    (fun k => hc k.unop.unop)
  unfold strictDiagramFreeArrowRealizedAugmentation
  rw [← Category.assoc, ← Category.assoc, h]
  change (bousfieldKanConeComparison
    (c.whisker (unopUnop (StrictDiagramArrowElements.{u} d))) ≫
      (bousfieldKanOpOpIso (StrictDiagramArrowElements.{u} d)
        (unopUnop (StrictDiagramArrowElements.{u} d) ⋙ strictDiagramFreeArrowHom A d X Y)).hom) ≫ _ = _
  rw [bousfieldKanOpOpIso_cone]
  change weightedConeComparison _ c ≫ _ = _
  have hn := weightedConeComparison_naturality
    (bousfieldKanWeight (StrictDiagramArrowElements.{u} d)) c
    (strictDiagramFrameArrowCone A d X Y) (𝟙 _) (strictDiagramFreeArrowHomNatIso A d X Y).hom
    (by
      intro k
      change 𝟙 _ ≫ (strictDiagramFrameArrowCone A d X Y).π.app k =
        ((strictDiagramFrameArrowCone A d X Y).π.app k ≫
          (strictDiagramFreeArrowHomIso A d X Y k).inv) ≫
            (strictDiagramFreeArrowHomIso A d X Y k).hom
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact hn.symm.trans (Category.id_comp _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
