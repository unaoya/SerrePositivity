module

public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.F1B.CofinalOppositeFibration
public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：right anodyne な元の射と任意の単体集合の直積。
方針：元の反転の left anodyne 性、既存の積の保存、反転の持ち上げ対応を使う。
規約：相手因子の充填性も元の射の単射性も追加しない。
使われ方：sifted な底の有限反復対角の cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- right anodyne な元の射と任意の右因子の直積は right anodyne。 -/
lemma rightAnodyneExtensions_whiskerRight {A B : SSet.{u}}
    (i : A ⟶ B) (hi : rightAnodyneExtensions i) (K : SSet.{u}) :
    rightAnodyneExtensions (i ▷ K) := by
  have hl := leftAnodyneExtensions_whiskerRight (SSet.opFunctor.map i)
    (cofinalLeftAnodyne_op_of_rightAnodyne i hi) K.op
  have he : SSet.opFunctor.map (i ▷ K) = (opTensorIso A K).inv ≫
      (SSet.opFunctor.map i ▷ K.op) ≫ (opTensorIso B K).hom := rfl
  have hop : leftAnodyneExtensions (SSet.opFunctor.map (i ▷ K)) := by
    rw [he]
    exact leftAnodyneExtensions.comp_mem _ _
      (MorphismProperty.of_isIso _ _) (leftAnodyneExtensions.comp_mem _ _ hl
        (MorphismProperty.of_isIso _ _))
  have hd := cofinalRightAnodyne_op_of_leftAnodyne (SSet.opFunctor.map (i ▷ K)) hop
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality (i ▷ K)
  change SSet.opFunctor.map (SSet.opFunctor.map (i ▷ K)) ≫
      (SSet.opFunctorCompOpFunctorIso.app (B ⊗ K)).hom =
    (SSet.opFunctorCompOpFunctorIso.app (A ⊗ K)).hom ≫ (i ▷ K) at hn
  have he' : (SSet.opFunctorCompOpFunctorIso.app (A ⊗ K)).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map (i ▷ K)) ≫
        (SSet.opFunctorCompOpFunctorIso.app (B ⊗ K)).hom = i ▷ K := by
    rw [hn, Iso.inv_hom_id_assoc]
  rw [← he']
  exact rightAnodyneExtensions.comp_mem _ _ (MorphismProperty.of_isIso _ _)
    (rightAnodyneExtensions.comp_mem _ _ hd (MorphismProperty.of_isIso _ _))

end SerrePositivity.InfinityCategories.HomotopyLimits
