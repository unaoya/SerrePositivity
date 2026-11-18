module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBKConeNaturality

/-!
概要：同じBK Hom図式の前後作用の単位・合成・交換則。
方針：元のsHom二変数関手とwhiskeringの全関手則を使う。
規約：IS-W2 D01の既存構成の単位・合成・貼り合わせ則。
使われ方：HA 1.2.4、指定錐のパラメータ図式の合成と高次単体の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable {A : Type u} [CommRing A]

/-- 同じ図式恒等射の実後合成は恒等。 -/
theorem enrichedBKHomTargetMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomTargetMap P (𝟙 X) = 𝟙 (enrichedBKHomDiagram P X) := by
  unfold enrichedBKHomTargetMap
  erw [Functor.whiskerLeft_id, Functor.whiskerRight_id]
  rfl

/-- 同じ図式射の実後合成は元の合成を保つ。 -/
theorem enrichedBKHomTargetMap_comp (P : Complex A)
    {X Y Z : CosimplicialObject (Complex A)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    enrichedBKHomTargetMap P (f ≫ g) =
      enrichedBKHomTargetMap P f ≫ enrichedBKHomTargetMap P g := by
  simp only [enrichedBKHomTargetMap, Functor.whiskerLeft_comp, Functor.whiskerRight_comp]

/-- 同じ頂点恒等射の実前合成は恒等。 -/
theorem enrichedBKHomSourceMap_id (P : Complex A) (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (𝟙 P) X = 𝟙 (enrichedBKHomDiagram P X) := by
  unfold enrichedBKHomSourceMap
  erw [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id]
  rfl

/-- 同じ頂点射の実前合成は反変の合成を保つ。 -/
theorem enrichedBKHomSourceMap_comp {P Q T : Complex A} (f : P ⟶ Q) (g : Q ⟶ T)
    (X : CosimplicialObject (Complex A)) :
    enrichedBKHomSourceMap (f ≫ g) X =
      enrichedBKHomSourceMap g X ≫ enrichedBKHomSourceMap f X := by
  simp only [enrichedBKHomSourceMap, Functor.map_comp, op_comp, Functor.whiskerLeft_comp]

/-- 同じ頂点射の前合成と図式射の後合成は厳密に可換。 -/
theorem enrichedBKHomSourceMap_targetMap {P Q : Complex A} (f : P ⟶ Q)
    {X Y : CosimplicialObject (Complex A)} (g : X ⟶ Y) :
    enrichedBKHomSourceMap f X ≫ enrichedBKHomTargetMap P g =
      enrichedBKHomTargetMap Q g ≫ enrichedBKHomSourceMap f Y := by
  apply NatTrans.ext
  funext j
  exact (((SimplicialCategory.sHomFunctor (ClosedCategory A (Complex A))).map
    ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map f).op).naturality
      ((_root_.SerrePositivity.ComplexLimits.complexToClosed A).map (g.app ((opOpEquivalence SimplexCategory).functor.obj j)))).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
