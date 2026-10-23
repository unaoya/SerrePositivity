module

public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramNativePointHomAction
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveActionNaturality
public import SerrePositivity.InfinityCategories.F1.Weighted.CommonWeightedNativePointedPrism
public import SerrePositivity.InfinityCategories.F1.Weighted.CommonWeightedHomAction

/-!
概要：native な反転後合成による weighted 作用を、元の共通 weighted Hom 作用へ戻す。
方針：一点 Hom 係数の全パラメーターの可換式を weighted nerve と宇宙移送へ渡す。
規約：元の Hom の同じ右端射影と元の両図式の標準係数同型を使う。
使われ方：構成した native pointed prism の終点条件を閉じる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 標準係数の weighted 同型の順射は、元の係数同型の順射を写した実際の weighted 射。 -/
lemma oppositePointHomWeightedIso_hom {I : Type u} [SmallCategory I]
    (F : I ⥤ KanObject.{u}) :
    (oppositePointHomWeightedIso F).hom = weightedNerveMap (oppositePointHomDiagramIso F).hom :=
  rfl

/-- native な反転係数の全 weighted 作用は、標準係数を介して元の全 weighted 作用と可換。 -/
lemma kanDiagramNativePointHomAction_weighted {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    (((weightedNerve (simplicialHomDiagram (F.val ⋙ kanObjectOpFunctor) pointKanObject ⋙
      SSet.opFunctor)) ◁ (kanDiagramNativeOppositeHomParameter F G ≫
        kanDiagramReflectedHomPostcomposition
          (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
          (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject)) ≫
      weightedNerveMappingFamily
        (simplicialHomDiagram (F.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)
        (simplicialHomDiagram (G.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)) ≫
      (oppositePointHomWeightedIso G.val).hom =
    ((oppositePointHomWeightedIso F.val).hom ▷ SimplicialCategory.sHom F G) ≫
      weightedNerveMappingFamily (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) := by
  have h := weightedNerveMappingFamily_intertwine
    (simplicialHomDiagram (F.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)
    (simplicialHomDiagram (G.val ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)
    (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)
    (kanDiagramNativeOppositeHomParameter F G ≫ kanDiagramReflectedHomPostcomposition
      (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
      (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject)
    (𝟙 (SimplicialCategory.sHom F G))
    (oppositePointHomDiagramIso F.val).hom (oppositePointHomDiagramIso G.val).hom
    (fun i => by simpa only [Category.id_comp] using
      kanDiagramNativePointHomAction_coefficient F G i)
  rw [oppositePointHomWeightedIso_hom, oppositePointHomWeightedIso_hom]
  simpa only [whiskerLeft_id, Category.comp_id, Category.id_comp] using h

/-- 共通 weighted 始域上でも、native な反転係数の作用は元の同じ Hom の作用と一致。 -/
lemma commonWeightedNativeHomAction_compare {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    ((strictKanCommonOppositeWeightedImage F.val ⊗ₘ
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)) ≫
        (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G))) ≫
      weightedKanHomCompositeFamily
        (show KanDiagramObject I from ⟨F.val ⋙ kanObjectOpFunctor, trivial⟩)
        (show KanDiagramObject I from ⟨G.val ⋙ kanObjectOpFunctor, trivial⟩) pointKanObject) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso G.val).hom =
    strictKanCommonWeightedHomFamily F G := by
  rw [strictKanCommonWeightedHomFamily_evaluation]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, h⟩
  apply ULift.ext
  exact congrArg (fun k => k.app (Opposite.op ⦋n⦌)
    (((strictKanCommonOppositeWeightedImage F.val).app _ s).down,
      (edgewiseRight (SimplicialCategory.sHom F G)).app _ h.down))
    (kanDiagramNativePointHomAction_weighted F G)

/-- 構成した native pointed prism の終点は、元の共通 weighted Hom 作用後の標的比較。 -/
lemma commonWeightedNativePointedPrism_one_eq {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) :
    (prismEndpoint 1 _ ▷ _) ≫ commonWeightedNativePointedPrism F G =
    strictKanCommonWeightedHomFamily F G ≫ oppositeKanUnstraighteningComparison G.val ≫
      CategoryTheory.Limits.pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) := by
  rw [commonWeightedNativePointedPrism_one]
  have h := commonWeightedNativeHomAction_compare F G
  have hi := congrArg (fun k => k ≫ (SSet.uliftFunctor.{u + 1, u}).map
    (oppositePointHomWeightedIso G.val).inv ≫
      strictKanUnstraighteningComparison (G.val ⋙ kanObjectOpFunctor) ≫
        CategoryTheory.Limits.pullback.fst pointedSpaceProjection
          (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))) h
  have he : (SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso G.val).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso G.val).inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    exact (SSet.uliftFunctor.{u + 1, u}).map_id _
  simp only [Category.assoc] at hi
  rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map
    (oppositePointHomWeightedIso G.val).hom), he, Category.id_comp] at hi
  simpa only [Category.assoc, oppositeKanUnstraighteningComparison] using hi

end SerrePositivity.InfinityCategories
