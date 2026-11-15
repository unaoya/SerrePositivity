module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafInclusion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：集合値 Yoneda を同じ離散前層埋め込みで空間値 Yoneda へ送る。
方針：通常の射列を Yoneda で写し、離散前層の全埋め込みを合成して反転する。
使われ方：HTT 5.1.5.6、Kerodon Corollary 5.6.0.6（Tag 028T）の重み付き切断の入口。
規約：元の小さい始域だけを持ち上げ、前層圏の宇宙を更に上げない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 元の離散埋め込みを、対象ごとの集合の写像の評価仕様とともに読む。 -/
def discretePresheafInclusion (C : Type u) [SmallCategory C] :
    {I : nerve (Cᵒᵖ ⥤ Type u) ⟶ PresheafCat C SpaceInfinity.{u} //
      (∀ P, I.app _ (nerveVertex P) = functorVertex (discretePresheaf P)) ∧
      (∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) (U : C),
        ((nerve.edgeMk φ).map (I ≫ evaluateFunctorAt (ULift.up (nerveVertex (Opposite.op U))))).edge =
          ((nerve.edgeMk (φ.app (Opposite.op U))).map discreteSpaceInclusion).edge)} := by
  let K := kanDiscretePresheafInclusion C
  refine ⟨K.val, K.property.1, ?_⟩
  intro P Q φ U
  exact discreteSpaceInclusion_presheafInclusion_edge K.val φ (K.property.2 φ) (Opposite.op U)

/-- 小さい通常圏の同じ Yoneda 埋め込みの全 nerve。 -/
def liftedSetYoneda (C : Type u) [SmallCategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ nerve (Cᵒᵖ ⥤ Type u) where
  app _ := ↾fun s ↦ s.down ⋙ yoneda
  naturality _ _ _ := rfl

/-- 重み付き切断の右 Kan 拡張を定める元の反対 Yoneda 射。 -/
def oppositeSpaceYoneda (C : Type u) [SmallCategory C] :
    presheafShape C ⟶ (PresheafCat C SpaceInfinity.{u}).op :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := C)).inv ≫
    (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve C)).hom ≫
    SSet.opFunctor.map (liftedSetYoneda C ≫ (discretePresheafInclusion C).val)

end SerrePositivity.InfinityCategories.Sheaves
