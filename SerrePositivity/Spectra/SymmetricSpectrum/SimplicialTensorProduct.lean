module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.SimplicialTensorUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointProduct
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorAssociator
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-!
# 直積による反復tensor・cotensorの比較

自由基点追加の直積比較と各段のsmashの結合同型から、直積によるtensorを反復作用へ移す。
反復tensorの合成随伴と右随伴の一意性から、cotensorの反復比較も構成する。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 直積によるtensorは、第二因子のtensor、第一因子のtensorの順の反復に自然に同型。 -/
def simplicialTensorProductNatIso (K L : SSet.{u}) :
    simplicialTensorFunctor (K ⊗ L) ≅ simplicialTensorFunctor L ⋙ simplicialTensorFunctor K :=
  pointwiseTensorBifunctor.mapIso (adjoinBasepointProductIso K L).symm ≪≫
    pointwiseTensorAssociatorNatIso (adjoinBasepoint K) (adjoinBasepoint L)

/-- 二つのtensor・cotensorの随伴を合成した反復作用の随伴。 -/
def simplicialTensorCotensorProductAdjunction (K L : SSet.{u}) :
    simplicialTensorFunctor L ⋙ simplicialTensorFunctor K ⊣
      simplicialCotensorFunctor K ⋙ simplicialCotensorFunctor L :=
  (simplicialTensorCotensorAdjunction L).comp (simplicialTensorCotensorAdjunction K)

/-- 直積によるcotensorは、第一因子、第二因子の順の反復に自然に同型。 -/
def simplicialCotensorProductNatIso (K L : SSet.{u}) :
    simplicialCotensorFunctor (K ⊗ L) ≅
      simplicialCotensorFunctor K ⋙ simplicialCotensorFunctor L :=
  ActionComparisonAdjunction.rightIso (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorProductAdjunction K L) (simplicialTensorProductNatIso K L)

/-- 直積によるcotensorの対象ごとの反復比較。 -/
def simplicialCotensorProductIso (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialCotensor (K ⊗ L) E ≅ simplicialCotensor L (simplicialCotensor K E) :=
  (simplicialCotensorProductNatIso K L).app E

/-- cotensorの直積比較もスペクトルの射に関して自然。 -/
@[reassoc] lemma simplicialCotensorProduct_naturality (K L : SSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) :
    (simplicialCotensorFunctor (K ⊗ L)).map f ≫ (simplicialCotensorProductIso K L F).hom =
    (simplicialCotensorProductIso K L E).hom ≫
      (simplicialCotensorFunctor L).map ((simplicialCotensorFunctor K).map f) :=
  (simplicialCotensorProductNatIso K L).hom.naturality f

/-- cotensorの反復比較が、tensorの逆比較を介して二つの評価を比較する法則。 -/
def simplicialCotensorProductEvaluationLaw (K L : SSet.{u})
    (E : SymmetricSpectrum.{u}) : Prop :=
  ActionComparisonAdjunction.evaluationLaw (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorProductAdjunction K L) (simplicialTensorProductNatIso K L) E

/-- cotensorの反復比較は、合成随伴の評価と直積による随伴の評価を保つ。 -/
lemma simplicialCotensorProduct_evaluation (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialCotensorProductEvaluationLaw K L E :=
  ActionComparisonAdjunction.rightIso_evaluation (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorProductAdjunction K L) (simplicialTensorProductNatIso K L) E

/-- 反復tensorからの射について、二つの転置をcotensorの比較で結ぶ法則。 -/
def simplicialCotensorProductHomEquivLaw (K L : SSet.{u})
    (E F : SymmetricSpectrum.{u})
    (f : simplicialTensor K (simplicialTensor L E) ⟶ F) : Prop :=
  ActionComparisonAdjunction.homEquivLaw (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorProductAdjunction K L) (simplicialTensorProductNatIso K L) E F f

/-- cotensorの反復比較は、直積の転置と反復tensorの合成随伴による転置を結ぶ。 -/
lemma simplicialCotensorProduct_homEquiv (K L : SSet.{u}) (E F : SymmetricSpectrum.{u})
    (f : simplicialTensor K (simplicialTensor L E) ⟶ F) :
    simplicialCotensorProductHomEquivLaw K L E F f :=
  ActionComparisonAdjunction.rightIso_homEquiv (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorProductAdjunction K L) (simplicialTensorProductNatIso K L) E F f

end SerrePositivity.SymmetricSpectrum
