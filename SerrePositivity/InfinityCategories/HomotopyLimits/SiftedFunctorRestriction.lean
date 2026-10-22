module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaYonedaInfinity

/-!
概要：小さい sifted 余極限を保つ全関手 ∞ 圏と、元の Yoneda による実際の制限射。
方針：元の全 native 余錐の保存性を関手頂点条件として取り、全部分包含と前合成を合成。
規約：元の全自然変換・高次単体を保持。accessible・presentable 性は含めない。
使われ方：P_Σ の全関手 ∞ 圏の普遍性で同値と証明すべき元の制限写像。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の全関手空間内の、小さい sifted 余極限を保つ頂点が張る全部分 ∞ 圏。 -/
def SiftedContinuousFunctorInfinity (X D : SSet.{u + 1}) : SSet.{u + 1} :=
  fullSubcomplexOnVertices ((ihom X).obj D)
    (fun v => PreservesSmallSiftedColimits ((functorVertexEquiv X D).symm v))

/-- 同じ保存関手の全部分 ∞ 圏は、元の高次自然変換を持つ quasicategory。 -/
instance siftedContinuousFunctorInfinity_quasicategory (X D : SSet.{u + 1}) [Quasicategory D] :
    Quasicategory (SiftedContinuousFunctorInfinity X D) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices ((ihom X).obj D)
    (fun v => PreservesSmallSiftedColimits ((functorVertexEquiv X D).symm v)) : SSet.{u + 1}))

/-- 元の保存関手の全部分 ∞ 圏から、同じ元の全関手空間への包含。 -/
def siftedContinuousFunctorInclusion (X D : SSet.{u + 1}) :
    SiftedContinuousFunctorInfinity X D ⟶ (ihom X).obj D :=
  (fullSubcomplexOnVertices _
    (fun v => PreservesSmallSiftedColimits ((functorVertexEquiv X D).symm v))).ι

/-- 同じ全部分包含は元の全写像空間で充満忠実。 -/
lemma siftedContinuousFunctorInclusion_isFullyFaithful (X D : SSet.{u + 1}) [Quasicategory D] :
    IsFullyFaithful (siftedContinuousFunctorInclusion X D) :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 普遍性で同値と判定する、元の P_Σ Yoneda による実際の制限射。 -/
def sigmaSiftedContinuousRestriction (C : SSet.{u}) [Quasicategory C] (D : SSet.{u + 1}) :
    SiftedContinuousFunctorInfinity (SigmaPresheafInfinity C) D ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D :=
  siftedContinuousFunctorInclusion (SigmaPresheafInfinity C) D ≫
    (pre (sigmaYonedaInfinityMap C)).app D

end SerrePositivity.InfinityCategories.HomotopyLimits
