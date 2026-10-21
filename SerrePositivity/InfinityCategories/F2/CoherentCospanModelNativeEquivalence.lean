module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelNativeLegCompatibility
public import SerrePositivity.InfinityCategories.F2.StrictPullbackIsoGluing

/-!
概要：元の実模型の二脚の指定比較を貼り合わせ、native 切断との全体の比較同型を作る。
方針：元の指定 path による底の整合を、右円柱・左指定類を保つ貼り合わせへ渡す。
規約：元の実比較そのものを使う。使われ方：各点の native 極限性から実模型の同値性へ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z) (b : B _⦋0⦌)
local notation "c" => coherentCospanConePointwiseCone F X Y Z C b
local notation "d" => joinInr Δ[0] (horn 2 2) ≫ Subtype.val c
local notation "f" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanLeftTarget d)
local notation "g" => relativeFunctorOverPre pointedSpaceProjection (relativeCospanRightTarget d)
local notation "N" => coherentCospanNativeSectionPullback F X Y Z C b
local notation "M" => coherentCospanModelNativeComparison F X Y Z C b
local instance : Fibration f := relativeCospanLeftTarget_fibration pointedSpaceProjection d
local instance : KanComplex (pullback f g) :=
  HomotopyLimits.kanComplex_of_iso (relativeCospanSectionsIso pointedSpaceProjection d)
local instance : KanComplex (vertexFiber (smallLeftUnstraighteningProjection F) b) :=
  vertexFiber_kanComplex_of_leftFibration _ _

/-- 元の同じ二脚の指定同型から、元の実模型比較と native 切断比較の全体を貼り合わせる。 -/
def coherentCospanModelNativeComparisonIso : FunctorIso N M :=
  Classical.choice (strictPullback_functorIso_exists f g N M
    (coherentCospanModelNativeLeftIso F X Y Z C b)
    (coherentCospanModelNativeRightIso F X Y Z C b)
    (coherentCospanModelNativeLegCompatibility F X Y Z C b))

/-- 各点の元の native 錐が極限なら、元の模型を切断側へ合成した実比較が同値。 -/
lemma coherentCospanModelNativeComparison_homotopyEquivalence (hc : IsLimitCone c) :
    IsSimplicialHomotopyEquivalence M := by
  have h := coherentCospanNativeSectionPullback_isQCatEquivalence F X Y Z C b hc
  exact (h.ofFunctorIso
    (coherentCospanModelNativeComparisonIso F X Y Z C b)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2
