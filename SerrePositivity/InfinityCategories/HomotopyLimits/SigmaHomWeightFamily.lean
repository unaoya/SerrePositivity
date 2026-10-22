module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaUniverseYoneda
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoYonedaConeLimits

/-!
概要：元の大きい Hom 係数前層への自然変換空間を、一つの全二変数の族にする。
方針：元の P_Σ の指定宇宙変更と、元の Hom 係数関手を共同 Hom で組み合わせる。
規約：元の全自然変換空間を保持。各対象対の写像空間だけで自然性を代用しない。
使われ方：元の左 Kan 延長の共同 Hom 右 Kan 族との全自然比較の相手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C : SSet.{u}} {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の P_Σ 前層から元の Hom 係数前層への、全二変数の自然変換空間の共同評価。 -/
def sigmaHomWeightJointEvaluation
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj (SigmaPresheafInfinity C)).op ⊗
      (SSet.uliftFunctor.{u + 3, u + 2}).obj ((SSet.uliftFunctor.{u + 2, u + 1}).obj D) ⟶
      SpaceInfinity.{u + 2} :=
  ((SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (sigmaUniverseInclusion C)) ⊗ₘ
    (SSet.uliftFunctor.{u + 3, u + 2}).map (presheafHomWeightDiagram F₀)) ≫
      homInfinityJointEvaluation (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C))

/-- 同じ全自然変換空間を、元の P_Σ の反変な全関手圏値の族として束ねる。 -/
def sigmaHomWeightFamily (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    (SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj (SigmaPresheafInfinity C)).op ⟶
      (ihom ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))).obj SpaceInfinity.{u + 2} :=
  (SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (sigmaUniverseInclusion C)) ≫
    coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      (pre ((SSet.uliftFunctor.{u + 3, u + 2}).map
        (presheafHomWeightDiagram F₀))).app SpaceInfinity.{u + 2}

/-- 同じ全族の展開は、元の二変数の全自然変換空間そのもの。 -/
lemma sigmaHomWeightFamily_uncurry (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    uncurry (sigmaHomWeightFamily F₀) =
      (β_ ((SSet.uliftFunctor.{u + 3, u + 2}).obj
        ((SSet.uliftFunctor.{u + 2, u + 1}).obj D))
        ((SSet.uliftFunctor.{u + 3, u + 2}).obj
          ((SSet.uliftFunctor.{u + 2, u + 1}).obj (SigmaPresheafInfinity C)).op)).hom ≫
            sigmaHomWeightJointEvaluation F₀ := by
  rw [sigmaHomWeightFamily, ← Category.assoc, uncurry_pre_app, uncurry_natural_left,
    coyonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 元の標的係数での全評価は、元の係数前層への全表現可能関手の制限。 -/
lemma sigmaHomWeightFamily_evaluation
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (d : ((SSet.uliftFunctor.{u + 2, u + 1}).obj D) _⦋0⦌) :
    sigmaHomWeightFamily F₀ ≫ evaluateFunctorAt (ULift.up d) =
      (SSet.uliftFunctor.{u + 3, u + 2}).map (SSet.opFunctor.map (sigmaUniverseInclusion C)) ≫
        representablePresheafInfinity ((presheafHomWeightDiagram F₀).app (Opposite.op ⦋0⦌) d) := by
  rw [sigmaHomWeightFamily, Category.assoc, Category.assoc, evaluateFunctorAt_pre]
  change (SSet.uliftFunctor.{u + 3, u + 2}).map
      (SSet.opFunctor.map (sigmaUniverseInclusion C)) ≫
    (coyonedaInfinityMap (PresheafInfinity ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫
      evaluateFunctorAt (ULift.up ((presheafHomWeightDiagram F₀).app (Opposite.op ⦋0⦌) d))) = _
  rw [coyonedaInfinityMap_evaluation]

end SerrePositivity.InfinityCategories.HomotopyLimits
