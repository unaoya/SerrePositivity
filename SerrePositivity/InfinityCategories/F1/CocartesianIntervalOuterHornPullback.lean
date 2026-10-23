module

public import SerrePositivity.InfinityCategories.F1.CocartesianIntervalOuterHornLift
public import SerrePositivity.InfinityCategories.F1.KanEquivalenceLiftingFibration
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberKan
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
概要：元の固定成分 Hom fiber は、第二三角形の外ホーン延長の実際の pullback。
方針：同じ二三角形の貼り合わせ・一意性を使い、外ホーン制限の持ち上げ性を移す。
規約：元の第一三角形への制限写像を変更しない。
使われ方：同じ可縮な合成三角形空間上の、実際の fiber 比較への帰着。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (intervalMappingSpace (coherentNerveVertex (cocartesianTransportDiagramValue F c))
  (coherentNerveVertex (cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (vertexFiber (cocartesianHomIntervalEvaluation F G c) v)

/-- 元の固定成分 Hom fiber の二三角形の制限は、同じ外ホーン制限の pullback。 -/
lemma cocartesianIntervalOuterHorn_isPullback :
    IsPullback (cocartesianIntervalSecondTriangleMap F G v)
      (cocartesianIntervalCompositionTriangleMap F G v)
      ((pre (horn 2 2).ι).app CatInfinity.{u}) (cocartesianIntervalOuterHornMap F G v) := by
  refine IsPullback.mk' (cocartesianIntervalOuterHornSquare F G v) ?_ ?_
  · intro T m n h₁ h₀
    apply cocartesianIntervalHomTriangle_hom_ext F G v m n
    · have hc := congrArg (fun a => innerTriangleExtensionUncurry a) h₀
      rw [cocartesianIntervalCompositionTriangleMap_uncurry,
        cocartesianIntervalCompositionTriangleMap_uncurry] at hc
      exact hc
    · have hc := congrArg (fun a => uncurry a) h₁
      rw [cocartesianIntervalSecondTriangleMap_uncurry,
        cocartesianIntervalSecondTriangleMap_uncurry] at hc
      exact hc
  · intro T a b h
    exact ⟨cocartesianIntervalOuterHornLift F G v a b h,
      cocartesianIntervalOuterHornLift_fst F G v a b h,
      cocartesianIntervalOuterHornLift_snd F G v a b h⟩

/-- 元の第一三角形への同じ制限写像は、単射な同値を右に持ち上げる。 -/
lemma kanEquivalenceLifting_cocartesianIntervalCompositionTriangleMap :
    F1B.KanEquivalenceLifting (cocartesianIntervalCompositionTriangleMap F G v) := by
  intro A B i hi he
  letI : HasLiftingProperty i ((pre (horn 2 2).ι).app CatInfinity.{u}) :=
    F1B.kanEquivalenceLifting_pre (horn 2 2).ι i hi he
  exact (cocartesianIntervalOuterHorn_isPullback F G v).hasLiftingProperty i

/-- 同じ可縮な合成三角形空間への、元の固定成分 fiber の制限写像は Kan fibration。 -/
lemma cocartesianIntervalCompositionTriangleMap_fibration :
    Fibration (cocartesianIntervalCompositionTriangleMap F G v) := by
  letI : Fibration (cocartesianHomIntervalEvaluation F G c) :=
    cocartesianHomIntervalEvaluation_fibration F G c
  letI : KanComplex E := vertexFiber_kanComplex_of_leftFibration _ _
  letI : KanComplex (cocartesianIntervalCompositionSpace F G v) :=
    (cocartesianIntervalCompositionSpace_isContractibleKan F G v).kanComplex
  exact fibration_of_kanEquivalenceLifting_of_kanComplex _
    (kanEquivalenceLifting_cocartesianIntervalCompositionTriangleMap F G v)

end SerrePositivity.InfinityCategories
