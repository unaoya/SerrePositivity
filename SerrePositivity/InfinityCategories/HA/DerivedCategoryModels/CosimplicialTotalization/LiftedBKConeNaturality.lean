module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKConeNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeCoherentCone

/-!
概要：native Tot錐の指定入力の全自然性を、実際のAsSmall添字とBK重み上で述べる。
方針：既存の指定添字関手による前合成と重みの射を、同じ全等式に適用する。
規約：IS-W2 D01の既存構成の自然性・係数移送則。入力・頂点・重みを選び直さない。
使われ方：HA 1.2.4、指定native錐族のパラメータ射と高次単体への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
variable {A : Type u} [CommRing A]

/-- 指定AsSmall添字へ、同じ反転実Hom図式を制限する。 -/
def liftedEnrichedBKHomDiagram (P : Complex A) (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} SimplexCategory ⥤ SSet.{u} :=
  (AsSmall.down ⋙ (opOpEquivalence SimplexCategory).inverse) ⋙
    enrichedBKHomDiagram P X ⋙ SimplicialObject.opFunctor

/-- 同じ図式射の後合成の、指定添字への像。 -/
def liftedEnrichedBKHomTargetMap (P : Complex A)
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBKHomDiagram P X ⟶ liftedEnrichedBKHomDiagram P Y :=
  Functor.whiskerLeft (AsSmall.down ⋙ (opOpEquivalence SimplexCategory).inverse)
    (Functor.whiskerRight (enrichedBKHomTargetMap P f) SimplicialObject.opFunctor)

/-- 同じ頂点射の前合成の、指定添字への像。 -/
def liftedEnrichedBKHomSourceMap {P Q : Complex A} (f : P ⟶ Q)
    (X : CosimplicialObject (Complex A)) :
    liftedEnrichedBKHomDiagram Q X ⟶ liftedEnrichedBKHomDiagram P X :=
  Functor.whiskerLeft (AsSmall.down ⋙ (opOpEquivalence SimplexCategory).inverse)
    (Functor.whiskerRight (enrichedBKHomSourceMap f X) SimplicialObject.opFunctor)

/-- native錐を作る同じ指定入力は、全図式射と同じTot射の両作用に両立する。 -/
theorem liftedEnrichedBousfieldKanCone_dinaturality
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y) :
    liftedEnrichedBousfieldKanCone X ≫
        liftedEnrichedBKHomTargetMap ((productTotalFunctor A).obj X) f =
      liftedEnrichedBousfieldKanCone Y ≫
        liftedEnrichedBKHomSourceMap ((productTotalFunctor A).map f) Y := by
  have h := congrArg (fun η =>
    smallBousfieldKanWeightDown SimplexCategory ≫
      Functor.whiskerLeft
        ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙
          (opOpEquivalence SimplexCategory).inverse) η)
    (enrichedBousfieldKanCone_dinaturality f)
  simp only [Functor.whiskerLeft_comp] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
