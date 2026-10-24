module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricPreservation
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexIso

/-!
概要：filtered・実現保存関手の全 ∞ 圏からの P_Σ Yoneda 制限同値。
方針：保存条件の同値を全部分複体の同型へ上げ、元の制限同値と合成する。
規約：元の包含と Yoneda 前合成を順射に保持する。
使われ方：P_Σ の filtered 余極限と幾何学的実現による普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：filtered 余極限と幾何学的実現を保つ関手の全部分 ∞ 圏。
方針：元の全関手圏の頂点に二種類の保存条件を課す。
規約：全自然変換と高次単体を保持する。
使われ方：二種類の生成操作による普遍性の始域。 -/
def FilteredGeometricFunctorInfinity (X D : SSet.{u + 1}) : SSet.{u + 1} :=
  fullSubcomplexOnVertices ((ihom X).obj D) (fun v ↦
    PreservesSmallKappaFilteredColimits Cardinal.aleph0 ((functorVertexEquiv X D).symm v) ∧
      PreservesSmallGeometricRealizations ((functorVertexEquiv X D).symm v))

/-- 概要：二種類の保存関手の全部分 ∞ 圏は quasicategory。
方針：関手圏の全部分複体の性質を使う。
規約：標的の quasicategory 性だけを要求する。
使われ方：普遍性同値の構成。 -/
instance filteredGeometricFunctorInfinity_quasicategory (X D : SSet.{u + 1})
    [Quasicategory D] : Quasicategory (FilteredGeometricFunctorInfinity X D) :=
  inferInstanceAs (Quasicategory (fullSubcomplexOnVertices ((ihom X).obj D) _ : SSet.{u + 1}))

/-- 概要：元の二種類の保存関手から元の全関手圏への包含。
方針：同じ頂点条件の全部分複体の包含を取る。
規約：元の全単体を変更しない。
使われ方：Yoneda 制限の実際の写像。 -/
def filteredGeometricFunctorInclusion (X D : SSet.{u + 1}) :
    FilteredGeometricFunctorInfinity X D ⟶ (ihom X).obj D :=
  (fullSubcomplexOnVertices _ _).ι

/-- 概要：二種類の保存関手からの元の Yoneda による制限。
方針：元の全部分包含と Yoneda 前合成を合成する。
規約：抽象的な同値への取り替えをしない。
使われ方：filtered・実現保存版の普遍性。 -/
def sigmaFilteredGeometricRestriction (C : SSet.{u}) [Quasicategory C] (D : SSet.{u + 1}) :
    FilteredGeometricFunctorInfinity (SigmaPresheafInfinity C) D ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D :=
  filteredGeometricFunctorInclusion (SigmaPresheafInfinity C) D ≫
    (pre (sigmaYonedaInfinityMap C)).app D

variable (C : SSet.{u}) [Quasicategory C]
  (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p)
  (D : SSet.{u + 1}) [Quasicategory D]
  (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
  (hDg : HasSmallGeometricRealizations D)

/-- 概要：二種類の保存関手と sifted 保存関手は同じ全関手空間内で同型。
方針：証明済みの保存条件同値を恒等関手上の全部分複体同型へ上げる。
規約：元の全自然変換を厳密に保持する。
使われ方：元の制限写像の同値性の移送。 -/
def sigmaFilteredGeometricFunctorIso :
    FilteredGeometricFunctorInfinity (SigmaPresheafInfinity C) D ≅
      SiftedContinuousFunctorInfinity (SigmaPresheafInfinity C) D :=
  fullSubcomplexIso (Iso.refl _) _ _ (fun v ↦
    (sigma_preservesSmallSiftedColimits_iff_filtered_geometric hC hD hDg
      ((functorVertexEquiv _ _).symm v)).symm)

include hC hD hDg in
/-- 概要：二種類の保存関手からの元の Yoneda 制限射自身は全 ∞ 圏同値。
方針：全部分複体の同型と既存の sifted 制限同値を合成する。
規約：標的には filtered 余極限と幾何学的実現のみを要求する。
使われ方：P_Σ の生成操作による完全な普遍性。 -/
lemma sigmaFilteredGeometricRestriction_isQCatEquivalence :
    IsQCatEquivalence (sigmaFilteredGeometricRestriction C D) := by
  have he : (sigmaFilteredGeometricFunctorIso C hC D hD hDg).hom ≫
      sigmaSiftedContinuousRestriction C D = sigmaFilteredGeometricRestriction C D := by
    dsimp only [sigmaFilteredGeometricFunctorIso, sigmaSiftedContinuousRestriction,
      siftedContinuousFunctorInclusion]
    rw [← Category.assoc, fullSubcomplexIso_hom_ι]
    change (filteredGeometricFunctorInclusion (SigmaPresheafInfinity C) D ≫ 𝟙 _) ≫
      (pre (sigmaYonedaInfinityMap C)).app D = _
    rw [Category.comp_id]
    rfl
  rw [← he]
  exact (qCatEquivalenceOfIso
    (sigmaFilteredGeometricFunctorIso C hC D hD hDg)).isQCatEquivalence.comp
    (sigmaSiftedContinuousRestriction_isQCatEquivalence_of_filtered_geometric C hC D hD hDg)

end SerrePositivity.InfinityCategories.F2.Presentable
