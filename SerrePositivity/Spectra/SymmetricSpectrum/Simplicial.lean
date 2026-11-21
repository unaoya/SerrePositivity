module

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
public import SerrePositivity.CategoryTheory.Enriched.BaseChange
public import SerrePositivity.Spectra.General.ParametrizedCotensor
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointProduct
public import SerrePositivity.Spectra.PointedSimplicialSet.AdjoinBasepointUnit
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.Basic

/-! # 単体集合による対称スペクトルの作用

概要：基点のない単体集合によるテンソル・余テンソル、単体的写像空間と随伴、
前合成・後合成、零次単体の比較、単位と直積による反復作用を扱う。
方針：自由基点追加と基点忘却を通じて、円周に特殊化した
`GeneralSymmetricSpectrum.pointwiseTensor`・`cotensor`・`mappingObject` と随伴を使う。
規約：写像空間の合成では最初に適用する射を第一因子に置く。
使われ方：スペクトルの単体的豊穣構造とレベルモデルの適合性。
-/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open GeneralSymmetricSpectrum (cotensor pointwiseTensor pointwiseTensorPost)
open PointedSimplicialSet
open scoped Simplicial

/-- 通常の単体的集合によるtensorは、自由な基点を追加した各段のsmash。 -/
def simplicialTensor (K : SSet.{u}) (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  pointwiseTensor (adjoinBasepoint K) E

/-- 通常の単体的集合によるcotensorは、自由な基点を追加した対象からのcotensor。 -/
def simplicialCotensor (K : SSet.{u}) (E : SymmetricSpectrum.{u}) : SymmetricSpectrum.{u} :=
  cotensor (adjoinBasepoint K) E

/-- 固定した単体的集合によるtensor関手。 -/
def simplicialTensorFunctor (K : SSet.{u}) : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  pointwiseTensorFunctor (adjoinBasepoint K)

/-- 固定した単体的集合によるcotensor関手。 -/
def simplicialCotensorFunctor (K : SSet.{u}) : SymmetricSpectrum.{u} ⥤ SymmetricSpectrum.{u} :=
  cotensorFunctor (adjoinBasepoint K)

/-- スペクトルを固定し、単体的集合を動かすtensor関手。 -/
def simplicialTensorParameterFunctor (E : SymmetricSpectrum.{u}) :
    SSet.{u} ⥤ SymmetricSpectrum.{u} :=
  adjoinBasepointFunctor ⋙ GeneralSymmetricSpectrum.mappingTensorFunctor E

/-- 基点を忘れた写像対象の値域スペクトルに関する関手。 -/
def simplicialMappingSpaceFunctor (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} ⥤ SSet.{u} :=
  GeneralSymmetricSpectrum.mappingObjectFunctor E ⋙ PointedSimplicialSet.forget

/-- tensorの単体的集合パラメータと通常の単体的写像対象の随伴。 -/
def simplicialTensorMappingAdjunction (E : SymmetricSpectrum.{u}) :
    simplicialTensorParameterFunctor E ⊣ simplicialMappingSpaceFunctor E :=
  adjoinBasepointAdjunction.comp (GeneralSymmetricSpectrum.mappingObjectAdjunction E)

/-- 単体的集合によるtensorとcotensorの随伴。 -/
def simplicialTensorCotensorAdjunction (K : SSet.{u}) :
    simplicialTensorFunctor K ⊣ simplicialCotensorFunctor K :=
  pointwiseTensorCotensorAdjunction (adjoinBasepoint K)

/-- 基点を忘れた通常の単体的写像対象。 -/
def simplicialMappingSpace (E F : SymmetricSpectrum.{u}) : SSet.{u} :=
  PointedSimplicialSet.forget.obj (GeneralSymmetricSpectrum.mappingObject E F)

/-- 通常の単体的写像対象の反変・共変の二変数関手。 -/
def simplicialMappingSpaceBifunctor : SymmetricSpectrum.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ SSet.{u} :=
  pointedMappingSpaceBifunctor ⋙
    (CategoryTheory.Functor.whiskeringRight _ _ _).obj PointedSimplicialSet.forget

/-- 通常の単体的写像対象の合成。最初に適用する射を第一因子に置く。 -/
def simplicialMappingComposition (E F G : SymmetricSpectrum.{u}) :
    simplicialMappingSpace E F ⊗ simplicialMappingSpace F G ⟶ simplicialMappingSpace E G :=
  (β_ (simplicialMappingSpace E F) (simplicialMappingSpace F G)).hom ≫
    PointedSimplicialSet.productToSmash (GeneralSymmetricSpectrum.mappingObject F G)
      (GeneralSymmetricSpectrum.mappingObject E F) ≫
      PointedSimplicialSet.forget.map (GeneralSymmetricSpectrum.mappingObjectComposition E F G)

/-- 通常のスペクトル射と単体的写像対象の零次単体の同値。 -/
def simplicialMappingVertexEquiv (E F : SymmetricSpectrum.{u}) :
    (E ⟶ F) ≃ (simplicialMappingSpace E F) _⦋0⦌ :=
  (GeneralSymmetricSpectrum.mappingObjectArrowEquiv E F).trans
    (PointedSimplicialSet.unitVertexEquiv (GeneralSymmetricSpectrum.mappingObject E F))

/-- 標準の零次単体のHom同値は、構成済みの零次単体の同値。 -/
lemma mappingSpaceSimplicialCategory_vertexEquiv (E F : SymmetricSpectrum.{u}) :
    let : EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
      pointedMappingEnrichedOrdinaryCategory
    let : SimplicialCategory SymmetricSpectrum.{u} :=
      TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
        SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
        PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}
    SimplicialCategory.homEquiv' E F = simplicialMappingVertexEquiv E F := by
  rfl

/-- 単体的集合の射をtensorの生成対象へ送る。 -/
def simplicialTensorPost {K L : SSet.{u}} (f : K ⟶ L) (E : SymmetricSpectrum.{u}) :
    simplicialTensor K E ⟶ simplicialTensor L E :=
  pointwiseTensorPost (adjoinBasepointFunctor.map f) E

/-- 単体的集合の射によるcotensorの前合成。 -/
def simplicialCotensorPre {K L : SSet.{u}} (f : K ⟶ L) (F : SymmetricSpectrum.{u}) :
    simplicialCotensor L F ⟶ simplicialCotensor K F :=
  ((GeneralSymmetricSpectrum.cotensorBifunctor (K := circle.{u})).map
    (adjoinBasepointFunctor.map f).op).app F

/-- 原変数スペクトルの射による通常の単体的写像対象の前合成。 -/
def simplicialMappingSpacePre {E E' : SymmetricSpectrum.{u}} (f : E' ⟶ E)
    (F : SymmetricSpectrum.{u}) : simplicialMappingSpace E F ⟶ simplicialMappingSpace E' F :=
  PointedSimplicialSet.forget.map ((pointedMappingSpaceBifunctor.map f.op).app F)

/-- 零次標準単体によるtensorは恒等関手に自然に同型。 -/
def simplicialTensorUnitNatIso :
    simplicialTensorFunctor (Δ[0] : SSet.{u}) ≅ 𝟭 SymmetricSpectrum.{u} :=
  pointwiseTensorBifunctor.mapIso adjoinBasepointDeltaZeroIso ≪≫ pointwiseTensorUnitNatIso

/-- 直積によるtensorは、第二因子のtensor、第一因子のtensorの順の反復に自然に同型。 -/
def simplicialTensorProductNatIso (K L : SSet.{u}) :
    simplicialTensorFunctor (K ⊗ L) ≅ simplicialTensorFunctor L ⋙ simplicialTensorFunctor K :=
  pointwiseTensorBifunctor.mapIso (adjoinBasepointProductIso K L).symm ≪≫
    pointwiseTensorAssociatorNatIso (adjoinBasepoint K) (adjoinBasepoint L)

end SerrePositivity.SymmetricSpectrum
