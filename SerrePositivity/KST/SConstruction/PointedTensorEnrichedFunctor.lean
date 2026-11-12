module
public import SerrePositivity.KST.SConstruction.PointedSSetObject
public import SerrePositivity.KST.SConstruction.ClosedTensorMappingLaws
public import SerrePositivity.KST.SConstruction.PointedSuspensionCoherentDiagram

/-! # 同じ固定左因子との smash の標準点つき厳密豊穣関手
概要：任意の点つき左因子との元の smash を、全 basedHom 作用を保つ豊穣関手にする。
方針：閉 Hom の tensor 作用の単位・合成を、元の忘却の monoidal 比較で移す。
規約：大域の豊穣 instance を変更しない。使われ方：基点固定の関手的円柱。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 任意の固定点つき左因子との smash は、標準点つきの厳密単体的豊穣関手。 -/
def pointedTensorEnrichedFunctor (K : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} where
  obj X := ⟨K ⊗ X.obj⟩
  map X Y := (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X.obj Y.obj).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id X.obj).right) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X.obj X.obj).right =
      PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id (K ⊗ X.obj)).right
    erw [Category.assoc, ← Under.comp_right, closedTensorMapping_id]
  map_comp X Y Z := by
    change PointedSimplicialSet.productToSmash _ _ ≫
      (MonoidalClosed.comp X.obj Y.obj Z.obj).right ≫
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X.obj Z.obj).right =
      ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X.obj Y.obj).right ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K Y.obj Z.obj).right) ≫
        PointedSimplicialSet.productToSmash _ _ ≫
        (MonoidalClosed.comp (K ⊗ X.obj) (K ⊗ Y.obj) (K ⊗ Z.obj)).right
    erw [← Under.comp_right, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.comp, Under.comp_right, ← Category.assoc,
      ← PointedSimplicialSet.productToSmash_naturality, Category.assoc]

/-- 元の全 tensor Hom の頂点作用は、元の同じ通常射の左 tensor を回収する。 -/
lemma pointedTensorMapping_vertex (K : PointedSimplicialSet.{u})
    {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y).right.app _ (Spectra.pointedHomVertexEquiv X Y f) =
      Spectra.pointedHomVertexEquiv (K ⊗ X) (K ⊗ Y) (K ◁ f) := by
  dsimp only [Spectra.pointedHomVertexEquiv, Equiv.trans_apply, curryHomEquiv']
  change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TensorMapping.map K X Y).right.app _
    (PointedSimplicialSet.unitVertexEquiv _ (curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, closedTensorMapping_curry']
  rfl

/-- 元の通常の点つき射では、全 Hom 作用から同じ左 smash 射を厳密に回収する。 -/
lemma pointedTensorEnrichedFunctor_hom (K : PointedSimplicialSet.{u})
    {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ (pointedTensorEnrichedFunctor K).map X Y =
      eHomEquiv SSet
        (show (pointedTensorEnrichedFunctor K).obj X ⟶ (pointedTensorEnrichedFunctor K).obj Y from
          K ◁ (show X.obj ⟶ Y.obj from f)) := by
  apply ((PointedObject.basedHom (K ⊗ X.obj) (K ⊗ Y.obj)).right.unitHomEquiv).injective
  exact pointedTensorMapping_vertex K (show X.obj ⟶ Y.obj from f)

end SerrePositivity.KST.SConstruction
