module

public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizedRelativeFunctorPullback
public import SerrePositivity.InfinityCategories.F1.Equivalences.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection

/-!
概要：局所化後の相対関手の全空間比較と、各指定底上の fiber 比較は同値。
方針：反転関手圏の同値を left fibration に沿って引き戻し、二対三則を使う。
規約：指定底を厳密に保つ比較射を使い、独立な fiber 逆写像を選ばない。
使われ方：一般初頂点写像による相対切断制限の同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {N A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  (f : N ⟶ A) (W : Set (N _⦋1⦌)) (hf : InvertsEdges f W)
  (p : E ⟶ B) [LeftFibration p] (hL : IsLocalization f W)
include hL

/-- 局所化後の相対関手の全空間比較は同値。 -/
lemma localizationRelativeTotalMap_isQCatEquivalence :
    IsQCatEquivalence (localizationRelativeTotalMap f W hf p) := by
  have hB : IsQCatEquivalence (localizationPrecomposition f W hf B) := hL.choose_spec B
  have hE : IsQCatEquivalence (localizationPrecomposition f W hf E) := hL.choose_spec E
  have hq : F1B.EquivalenceLifting (invertingFunctorPostcomp p W) :=
    leftFibration_equivalenceLifting (invertingFunctorPostcomp p W)
  have hs := (hB.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting
    (invertingFunctorPostcomp p W) hq).isQCatEquivalence
  have : Quasicategory (localizationRelativeTotal f W hf p) :=
    quasicategory_of_innerFibration (localizationRelativeProjection f W hf p)
  apply hs.cancel_right
  rw [localizationRelativeTotalMap_restriction]
  exact hE

/-- 同じ底の指定関手上の fiber 比較も同値。 -/
lemma localizationRelativeTotalMap_fiber_isQCatEquivalence (b : A ⟶ B) :
    IsQCatEquivalence (vertexFiberMap ((ihom A).map p)
      (localizationRelativeProjection f W hf p) (localizationRelativeTotalMap f W hf p)
      (localizationRelativeTotalMap_projection f W hf p) (functorVertex b)) := by
  exact vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence ((ihom A).map p)
    (localizationRelativeProjection f W hf p) (localizationRelativeTotalMap f W hf p)
    (localizationRelativeTotalMap_projection f W hf p)
    (localizationRelativeTotalMap_isQCatEquivalence f W hf p hL).isPrecompositionEquivalence
    (functorVertex b)

end SerrePositivity.InfinityCategories
