module

public import SerrePositivity.InfinityCategories.F2.Ind.NativeFilteredPreservation

/-!
概要：κ-filtered 余極限を保つ関手の全部分 ∞ 圏と、元の Yoneda による実際の制限射。
方針：元の native 保存性を頂点条件として取り、包含と内部 Hom の前合成を合成する。
規約：Indκ と標的 D は宇宙 u+1、κ と試験添字は u。この射の同値性は後続で証明する。
使われ方：HTT 5.3.5.10 の普遍性で同値と証明すべき元の写像。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ元の関手空間の、κ-filtered 余極限を保つ頂点が張る全部分複体。 -/
def KappaContinuousFunctorInfinity (κ : Cardinal.{u}) (X D : SSet.{u + 1}) : SSet.{u + 1} :=
  fullSubcomplexOnVertices ((ihom X).obj D)
    (fun v => PreservesSmallKappaFilteredColimits κ ((functorVertexEquiv X D).symm v))

instance kappaContinuousFunctorInfinity_quasicategory (κ : Cardinal.{u})
    (X D : SSet.{u + 1}) [Quasicategory D] :
    Quasicategory (KappaContinuousFunctorInfinity κ X D) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices ((ihom X).obj D)
    (fun v => PreservesSmallKappaFilteredColimits κ ((functorVertexEquiv X D).symm v)) :
      SSet.{u + 1}))

/-- 保存関手の全部分 ∞ 圏から、元の全関手空間への包含。 -/
def kappaContinuousFunctorInclusion (κ : Cardinal.{u}) (X D : SSet.{u + 1}) :
    KappaContinuousFunctorInfinity κ X D ⟶ (ihom X).obj D :=
  (fullSubcomplexOnVertices _
    (fun v => PreservesSmallKappaFilteredColimits κ ((functorVertexEquiv X D).symm v))).ι

/-- 全部分包含は、元の関手同士の全写像空間に対して充満忠実。 -/
lemma kappaContinuousFunctorInclusion_isFullyFaithful (κ : Cardinal.{u})
    (X D : SSet.{u + 1}) [Quasicategory D] :
    IsFullyFaithful (kappaContinuousFunctorInclusion κ X D) :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- 普遍性の対象となる、元の Yoneda に沿う実際の制限写像。 -/
def indKappaContinuousRestriction (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C]
    (D : SSet.{u + 1}) :
    KappaContinuousFunctorInfinity κ (IndInfinity κ C) D ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D :=
  kappaContinuousFunctorInclusion κ (IndInfinity κ C) D ≫ (pre (indYoneda κ C)).app D

end SerrePositivity.InfinityCategories.F2.Ind
