module
public import SerrePositivity.InfinityCategories.Derived.DGKappaNativePFamily
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalStageSupply

/-!
概要：実 Morita／P 全族を、K-B3 が採用した新 sphere-only 段提供者へ特殊化する。
方針：追加の比較入力なしで、元の全族と各入力の同じ新 cone・P を厳密に回収する。
規約：核の StableInfinity 値は構成した終点作用であり、S 内の核角作用との一致は未供給。
全四角形と square_at の存在をこの特殊化だけで主張しない。
使われ方：D-4b の新模型における実 Morita／P 比較族。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)

/-- 新模型で、固定 ν を始点とする実 Morita 比較の全 native 入力族。 -/
def dgKappaSphereClosureNativeMoritaFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    equivalencePath StableInfinity.{max (u + 1) v} :=
  dgKappaNativeMoritaFamily R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

lemma dgKappaSphereClosureNativeMoritaFamily_source :
    dgKappaSphereClosureNativeMoritaFamily.{u, v} R κ hκ ≫ equivalencePathEndpoint _ 0 =
      dgKInputNu R :=
  dgKappaNativeMoritaFamily_source R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

lemma dgKappaSphereClosureNativeMoritaFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaSphereClosureNativeMoritaFamily R κ hκ).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex A) =
      equivalencePathVertex (stableArrow (dgKappaNativeMoritaExactMap R A
        (dgKappaConeInput_unconditional' R A κ hκ)
        (dgKappaPerfectInput_unconditional' R A κ hκ)))
        (dgKappaNativeMoritaExactMap_isInvertible R A
          (dgKappaConeInput_unconditional' R A κ hκ)
          (dgKappaPerfectInput_unconditional' R A κ hκ)) :=
  dgKappaNativeMoritaFamily_at R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A

/-- 新模型の実核の StableInfinity 値の全作用。S 内への持ち上げは別工程。 -/
def dgKappaSphereClosureNativeKernelStableFamily :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ StableInfinity.{max (u + 1) v} :=
  dgKappaNativeKernelStableFamily R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

lemma dgKappaSphereClosureNativeKernelStableFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaSphereClosureNativeKernelStableFamily R κ hκ).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex A) = stableVertex (dgKInputStableValue R
      (dgKappaResolvedKernelKInput R A (dgKappaConeInput_unconditional' R A κ hκ))) :=
  dgKappaNativeKernelStableFamily_at R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A

/-- 新模型の全 native 入力に自然な実 Morita 同型。 -/
def dgKappaSphereClosureNativeMoritaIso :
    FunctorIso (dgKInputNu R) (dgKappaSphereClosureNativeKernelStableFamily.{u, v} R κ hκ) :=
  dgKappaNativeMoritaFamily_iso R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

/-- 新模型の元の P/Yoneda 比較を全 native 入力で保持する全族。 -/
def dgKappaSphereClosureNativePComparisonFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
      StableInfinity.{max (u + 1) v}) :=
  dgKappaNativePComparisonFamily R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

lemma dgKappaSphereClosureNativePComparisonFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaSphereClosureNativePComparisonFamily R κ hκ).app (Opposite.op ⦋0⦌)
        (coherentNerveVertex A) = dgKappaNativePComparisonPath R A
      (dgKappaConeInput_unconditional' R A κ hκ)
      (dgKappaPerfectInput_unconditional' R A κ hκ) :=
  dgKappaNativePComparisonFamily_at R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) A

lemma dgKappaSphereClosureNativePComparisonFamily_boundary :
    dgKappaSphereClosureNativePComparisonFamily.{u, v} R κ hκ ≫
        equivalencePathMap ((pre (boundary 1).ι).app StableInfinity.{max (u + 1) v}) =
      (dgKappaNativeMoritaArrowFamily R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ) ≫
        (pre (boundary 1).ι).app _) ≫ equivalencePathRefl _ :=
  dgKappaNativePComparisonFamily_boundary R (dgKappaUnconditionalStageProvider.{u, v} R κ hκ)

end SerrePositivity.InfinityCategories
