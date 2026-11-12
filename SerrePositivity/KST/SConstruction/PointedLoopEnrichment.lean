module
public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-! # Loop の点つき豊穣作用
概要：loop が基点固定写像空間へ誘導する射を全単体次数で構成する。
方針：円からの内部 Hom の合成を curry し、単位と合成の保存を評価で証明する。
規約：点つきの元の loop 模型を使い、対象の Kan 性はここでは不要。
使われ方：coherent nerve 上の loop 関手と、全入力の Ω 構造の標的の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Spectra
open scoped Simplicial

/-- Loop が点つき内部 Hom に誘導する全単体の作用。 -/
def pointedLoopHom (X Y : PointedSimplicialSet.{u}) :
    PointedObject.basedHom X Y ⟶ PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) :=
  curry (MonoidalClosed.comp PointedSimplicialSet.circle.{u} X Y)

/-- Loop の写像空間の作用を評価すると元の内部 Hom の合成になる。 -/
lemma pointedLoopHom_evaluation (X Y : PointedSimplicialSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X ◁ pointedLoopHom X Y ≫ (ihom.ev (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X)).app (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) =
      MonoidalClosed.comp PointedSimplicialSet.circle.{u} X Y :=
  uncurry_curry (MonoidalClosed.comp PointedSimplicialSet.circle.{u} X Y)

/-- Loop の写像空間の作用は通常の点つき射への loop の作用を回収する。 -/
lemma pointedLoopHom_curry' {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    curry' f ≫ pointedLoopHom X Y =
      curry' ((ihom PointedSimplicialSet.circle.{u}).map f) := by
  apply uncurry_injective
  rw [uncurry_natural_left, pointedLoopHom, uncurry_curry]
  conv_rhs => rw [curry', uncurry_curry]
  exact whiskerLeft_curry'_comp f

/-- Loop の全写像パラメータへの作用は豊穣単位を保つ。 -/
lemma pointedLoopHom_id (X : PointedSimplicialSet.{u}) :
    MonoidalClosed.id X ≫ pointedLoopHom X X = MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) := by
  change MonoidalClosed.id X ≫ pointedLoopHom X X =
    MonoidalClosed.id ((ihom PointedSimplicialSet.circle.{u}).obj X)
  have h := pointedLoopHom_curry' (𝟙 X)
  have hm : (ihom PointedSimplicialSet.circle.{u}).map (𝟙 X) =
      𝟙 ((ihom PointedSimplicialSet.circle.{u}).obj X) := CategoryTheory.Functor.map_id _ _
  rw [hm] at h
  simpa only [curry'_id] using h

/-- Loop の全写像パラメータへの作用は豊穣合成を保つ。 -/
lemma pointedLoopHom_comp (X Y Z : PointedSimplicialSet.{u}) :
    MonoidalClosed.comp X Y Z ≫ pointedLoopHom X Z =
      (pointedLoopHom X Y ⊗ₘ pointedLoopHom Y Z) ≫
        MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) := by
  change MonoidalClosed.comp X Y Z ≫ curry
      (MonoidalClosed.comp PointedSimplicialSet.circle.{u} X Z) =
    (curry (MonoidalClosed.comp PointedSimplicialSet.circle.{u} X Y) ⊗ₘ
      curry (MonoidalClosed.comp PointedSimplicialSet.circle.{u} Y Z)) ≫
        MonoidalClosed.comp ((ihom PointedSimplicialSet.circle.{u}).obj X)
          ((ihom PointedSimplicialSet.circle.{u}).obj Y)
          ((ihom PointedSimplicialSet.circle.{u}).obj Z)
  apply uncurry_injective
  simp only [uncurry_natural_left]
  conv_lhs => rw [uncurry_curry]
  conv_rhs =>
    arg 2
    rw [comp_eq, uncurry_curry, compTranspose_eq]
  rw [tensorHom_def, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, associator_inv_naturality_middle_assoc,
    whisker_exchange_assoc, ← comp_whiskerRight_assoc, whiskerLeft_curry_ihom_ev_app]
  dsimp only [Functor.id_obj]
  rw [whiskerLeft_curry_ihom_ev_app]
  exact (MonoidalClosed.assoc PointedSimplicialSet.circle.{u} X Y Z).symm

/-- Loop の写像空間の作用は、頂点で元の通常の loop 射を回収する。 -/
lemma pointedLoopHom_vertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (pointedLoopHom X Y).right.app _ (pointedHomVertexEquiv X Y f) =
      pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)
        ((ihom PointedSimplicialSet.circle.{u}).map f) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, curryHomEquiv']
  change (pointedLoopHom X Y).right.app _
    (PointedSimplicialSet.unitVertexEquiv _ (curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, pointedLoopHom_curry']
  rfl

local instance pointedLoopUnderlying_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- Loop は通常の単体集合で豊穣化した合成を保つ。 -/
lemma pointedLoopHom_simplicial_comp (X Y Z : PointedSimplicialSet.{u}) :
    eComp SSet X Y Z ≫ (pointedLoopHom X Z).right =
      ((pointedLoopHom X Y).right ⊗ₘ (pointedLoopHom Y Z).right) ≫
        eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z) := by
  change PointedSimplicialSet.productToSmash _ _ ≫
      (MonoidalClosed.comp X Y Z).right ≫ (pointedLoopHom X Z).right =
    ((pointedLoopHom X Y).right ⊗ₘ (pointedLoopHom Y Z).right) ≫
      PointedSimplicialSet.productToSmash _ _ ≫
        (MonoidalClosed.comp (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Z)).right
  rw [← Under.comp_right, pointedLoopHom_comp, Under.comp_right, ← Category.assoc,
    ← PointedSimplicialSet.productToSmash_naturality, Category.assoc]

/-- Loop は通常の単体集合で豊穣化した単位を保つ。 -/
lemma pointedLoopHom_simplicial_id (X : PointedSimplicialSet.{u}) :
    eId SSet X ≫ (pointedLoopHom X X).right = eId SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X) := by
  change (PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id X).right) ≫
      (pointedLoopHom X X).right =
    PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace X)).right
  rw [Category.assoc, ← Under.comp_right, pointedLoopHom_id]

/-- 元の loop 対象と全写像空間の作用を持つ単体的豊穣関手。 -/
def pointedLoopEnrichedFunctor :
    EnrichedFunctor SSet.{u} PointedSimplicialSet.{u} PointedSimplicialSet.{u} where
  obj := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace
  map X Y := (pointedLoopHom X Y).right
  map_id := pointedLoopHom_simplicial_id
  map_comp := pointedLoopHom_simplicial_comp

end SerrePositivity.KST.SConstruction
