module
public import SerrePositivity.KST.SConstruction.RawSmashEvaluation
public import SerrePositivity.KST.SConstruction.SuspensionAdjointInterval
public import SerrePositivity.KST.SConstruction.KanAssemblyAdjoint

/-! # 元の assembly の随伴の区間上の評価
概要：元の構造射と Kan 標的への随伴射を、元の区間と実現の積上で回収する。
方針：二つの cofiber の降下の評価と suspension 随伴の評価を合成する。
規約：構成済みの随伴と商射を使う。使われ方：零行収縮による loop 射との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial

/-- 元の suspension の構造射は元の区間族を厳密に回収する。 -/
lemma oneDirectionSuspensionAssembly_evaluation (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      oneDirectionReductionQuotient r X) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          (oneDirectionReducedRealization r X)).right ≫
            (oneDirectionSuspensionAssembly r X).right =
      multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X :=
  rawCofiberTensorDesc_evaluation _ _ _ _ _ _

/-- 元の随伴を円の区間商上で評価すると元の区間 assembly になる。 -/
lemma oneDirectionAssemblyAdjoint_interval (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      (oneDirectionRealizationFunctor (r + 1)).obj X) ≫
        uncurry ((oneDirectionReductionQuotient r X ≫
          (oneDirectionAssemblyAdjoint r X).right) ≫
            PointedObject.basedHomι PointedSimplicialSet.circle.{u}
              (boundaryReducedRealization (r + 1) X)) =
      multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X := by
  rw [oneDirectionAssemblyAdjoint, suspensionLoopEquiv_interval,
    oneDirectionSuspensionAssembly_evaluation]

/-- loop 射の区間上の評価は標的の点つき射との後合成を保つ。 -/
lemma loop_interval_postcomp {A : SSet.{u}} {B C : PointedSimplicialSet.{u}}
    (f : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right) (k : B ⟶ C) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      uncurry ((f ≫ ((PointedObject.basedHomFunctor
        PointedSimplicialSet.circle.{u}).map k).right) ≫
          PointedObject.basedHomι PointedSimplicialSet.circle.{u} C) =
      ((PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
        uncurry (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B)) ≫
          k.right := by
  change _ ≫ uncurry ((f ≫ (PointedObject.basedHomMap _ k).right) ≫ _) = _
  rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc]
  have hc := uncurry_natural_right
    (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) k.right
  rw [hc, Category.assoc]

/-- Kan 標的への元の随伴射も元の区間 assembly と Kan 単位を回収する。 -/
lemma kanTargetAssemblyAdjoint_interval (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      (oneDirectionRealizationFunctor (r + 1)).obj X) ≫
        uncurry ((oneDirectionReductionQuotient r X ≫
          ((kanTargetAssemblyAdjointNat r).app X).right) ≫
            PointedObject.basedHomι PointedSimplicialSet.circle.{u}
              ((boundaryKanRealizationFunctor (r + 1)).obj X)) =
      multiDiagonalAssembly (r + 1) X ≫ boundaryReductionQuotient (r + 1) X ≫
        (Spectra.PointedKanReplacement.unit.app
          (boundaryReducedRealization (r + 1) X)).right := by
  change _ ≫ uncurry ((_ ≫ ((oneDirectionAssemblyAdjoint r X).right ≫
    ((PointedObject.basedHomFunctor PointedSimplicialSet.circle.{u}).map
      (Spectra.PointedKanReplacement.unit.app
        (boundaryReducedRealization (r + 1) X))).right)) ≫ _) = _
  rw [← Category.assoc (oneDirectionReductionQuotient r X)]
  have hc := loop_interval_postcomp
    (oneDirectionReductionQuotient r X ≫ (oneDirectionAssemblyAdjoint r X).right)
    (Spectra.PointedKanReplacement.unit.app (boundaryReducedRealization (r + 1) X))
  rw [oneDirectionAssemblyAdjoint_interval, Category.assoc] at hc
  exact hc

/-- loop 射の区間上の評価はパラメータの前合成を保つ。 -/
lemma loop_interval_precomp {A A' : SSet.{u}} (B : PointedSimplicialSet.{u})
    (a : A ⟶ A') (f : A' ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      uncurry ((a ≫ f) ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
      ((Δ[1] : SSet.{u}) ◁ a) ≫
        (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A') ≫
          uncurry (f ≫ PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) := by
  rw [Category.assoc, uncurry_natural_left, ← Category.assoc,
    ← whisker_exchange, Category.assoc]

end SerrePositivity.KST.SConstruction
