module

public import SerrePositivity.InfinityCategories.F1.Coherent.TwoSidedHomLeftEndpoint
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：豊穣図式を実現した後でも、元の左右 Hom 区間比較は共通解像上で関手同型。
方針：固定端点の補間を同じ共同実現へ後合成し、変換空間の Kan 性を使う。
規約：始域の変換空間の Kan 性や対象ごとの比較の選択を仮定しない。
使われ方：元の反転 unstraightening の右 Hom 作用を native な左 Hom 輸送へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の左 Hom 区間の全体を、指定された元の strict 図式間の変換空間へ実現する。 -/
def kanEnrichedDiagramLeftHomInterval {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I)
    (X Y : C) {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y).op ⟶
      leftUnstraighteningTransformationSpace (kanDiagramCoherentNerve F)
        (kanDiagramCoherentNerve G) :=
  coherentCosliceFiberComparison X Y ≫
    cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫
    intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
      ((D.realization_vertex X).trans (congrArg (fun F => functorVertex
        (kanDiagramCoherentNerve F)) hF))
      ((D.realization_vertex Y).trans (congrArg (fun G => functorVertex
        (kanDiagramCoherentNerve G)) hG))

/-- 全 Hom の同じ共通解像上で、共同実現後の元の左右区間族を結ぶホモトピー。 -/
def kanEnrichedDiagramTwoSidedHomIntervalHomotopy {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I)
    (X Y : C) {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    SSet.Homotopy
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        kanEnrichedDiagramLeftHomInterval D X Y hF hG)
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
        kanEnrichedDiagramHomInterval D X Y hF hG) := by
  let p := intervalMappingPostOfEq D.realization (coherentNerveVertex X) (coherentNerveVertex Y)
    ((D.realization_vertex X).trans (congrArg (fun F => functorVertex
      (kanDiagramCoherentNerve F)) hF))
    ((D.realization_vertex Y).trans (congrArg (fun G => functorVertex
      (kanDiagramCoherentNerve G)) hG))
  let H := coherentTwoSidedHomIntervalHomotopy X Y
  refine { h := H.h ≫ p, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ (H.h ≫ p) =
      (SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        coherentCosliceFiberComparison X Y ≫
          cosliceFiberToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫ p
    simpa only [Category.assoc] using congrArg (fun f => f ≫ p) H.h₀
  · change SSet.ι₁ ≫ (H.h ≫ p) =
      (SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
        coherentHomComparison X Y ≫
          pinchedHomToIntervalMappingSpace (coherentNerveVertex X) (coherentNerveVertex Y) ≫ p
    simpa only [Category.assoc] using congrArg (fun f => f ≫ p) H.h₁
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 共同実現後の左右 Hom 区間の比較は、全 Hom の共通解像上の関手同型。 -/
def kanEnrichedDiagramTwoSidedHomIntervalIso {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I)
    (X Y : C) {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseLeft (SimplicialCategory.sHom X Y)) ≫
        kanEnrichedDiagramLeftHomInterval D X Y hF hG)
      ((SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom X Y)) ≫
        kanEnrichedDiagramHomInterval D X Y hF hG) :=
  functorIsoOfSimplicialHomotopy
    (kanEnrichedDiagramTwoSidedHomIntervalHomotopy D X Y hF hG)

end SerrePositivity.InfinityCategories
