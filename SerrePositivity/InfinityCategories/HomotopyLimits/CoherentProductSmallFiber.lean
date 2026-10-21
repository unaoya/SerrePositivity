module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentProductPointedFiber
public import SerrePositivity.InfinityCategories.HomotopyLimits.SmallPointedFiberNaturality

/-!
概要：点ごとの coherent 積の元の小さい全空間作用は、各 fiber で二つの fiber の積への同値。
方針：縮小の fiber 同型と厳密に可換な二射影を組にし、普遍 fiber の同値性を反映する。
規約：底は任意の小さい単体集合。使われ方：元の pullback への比較射の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
attribute [local instance] vertexFiber_kanComplex_of_leftFibration kanTensor_isKan
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)

/-- 元の指定全空間作用を小さい fiber に制限して組にする。 -/
def coherentProductSmallFiberMap :
    vertexFiber (smallLeftUnstraighteningProjection (coherentSpaceTensorProduct F G)) b ⟶
      vertexFiber (smallLeftUnstraighteningProjection F) b ⊗
        vertexFiber (smallLeftUnstraighteningProjection G) b :=
  lift
    (vertexFiberMap _ _ (coherentSpaceTensorProductTotalFst F G)
      (F2.coherentTransformationTotalMap_projection _ _ _) b)
    (vertexFiberMap _ _ (coherentSpaceTensorProductTotalSnd F G)
      (F2.coherentTransformationTotalMap_projection _ _ _) b)

/-- 元の小さい二射影の対は、持ち上げた普遍 fiber の同じ対と厳密に可換。 -/
lemma coherentProductSmallFiberMap_pointed :
    (SSet.uliftFunctor.{u + 1, u}).map (coherentProductSmallFiberMap F G b) ≫
      (uliftTensorIso (vertexFiber (smallLeftUnstraighteningProjection F) b)
        (vertexFiber (smallLeftUnstraighteningProjection G) b)).hom ≫
      ((smallPointedFiberIso F b).hom ⊗ₘ (smallPointedFiberIso G b).hom) =
        (smallPointedFiberIso (coherentSpaceTensorProduct F G) b).hom ≫
          coherentProductPointedFiberMap F G b := by
  apply CartesianMonoidalCategory.hom_ext
  · calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (vertexFiberMap _ _ (coherentSpaceTensorProductTotalFst F G)
            (F2.coherentTransformationTotalMap_projection _ _ _) b) ≫
          (smallPointedFiberIso F b).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        rfl
      _ = _ := by
        have h := smallPointedFiberIso_naturality (coherentSpaceTensorProduct F G) F
          (coherentSpaceTensorProductFstVertex F G) b
        simpa only [coherentSpaceTensorProductTotalFst,
          coherentProductPointedFiberMap, Category.assoc, lift_fst] using h
  · calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (vertexFiberMap _ _ (coherentSpaceTensorProductTotalSnd F G)
            (F2.coherentTransformationTotalMap_projection _ _ _) b) ≫
          (smallPointedFiberIso G b).hom := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro s
        rfl
      _ = _ := by
        have h := smallPointedFiberIso_naturality (coherentSpaceTensorProduct F G) G
          (coherentSpaceTensorProductSndVertex F G) b
        simpa only [coherentSpaceTensorProductTotalSnd,
          coherentProductPointedFiberMap, Category.assoc, lift_snd] using h

/-- 同じ小さい全空間作用の二つの fiber 射の対は、元の宇宙で同値。 -/
lemma coherentProductSmallFiberMap_isQCatEquivalence :
    IsQCatEquivalence (coherentProductSmallFiberMap F G b) := by
  have h := (qCatEquivalenceOfIso
    (smallPointedFiberIso (coherentSpaceTensorProduct F G) b)).isQCatEquivalence.comp
      (coherentProductPointedFiberMap_isQCatEquivalence F G b)
  change IsQCatEquivalence
    ((smallPointedFiberIso (coherentSpaceTensorProduct F G) b).hom ≫
      coherentProductPointedFiberMap F G b) at h
  rw [← coherentProductSmallFiberMap_pointed] at h
  have ht := (qCatEquivalenceOfIso
    (uliftTensorIso (vertexFiber (smallLeftUnstraighteningProjection F) b)
      (vertexFiber (smallLeftUnstraighteningProjection G) b))).isQCatEquivalence.comp
        (tensor_isQCatEquivalence
          (qCatEquivalenceOfIso (smallPointedFiberIso F b)).isQCatEquivalence
          (qCatEquivalenceOfIso (smallPointedFiberIso G b)).isQCatEquivalence)
  exact (isQCatEquivalence_ulift_iff_of_kan _).mp (ht.cancel_right h)

end SerrePositivity.InfinityCategories.HomotopyLimits
