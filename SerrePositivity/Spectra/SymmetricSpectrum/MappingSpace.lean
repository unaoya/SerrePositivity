module

public import SerrePositivity.Spectra.General.PointwiseTensorCoherence
public import SerrePositivity.Spectra.SymmetricSpectrum.PointwiseTensorFunctor
public import SerrePositivity.Spectra.SymmetricSpectrum.InternalHomFunctor
public import SerrePositivity.Spectra.General.ParametrizedCotensor
public import Mathlib.CategoryTheory.Whiskering
public import SerrePositivity.CategoryTheory.Adjunction.Comparison
public import SerrePositivity.CategoryTheory.Enriched.RepresentedMapping

/-! # 基点付き写像対象と各段のsmashの表現性 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open GeneralSymmetricSpectrum (pointwiseTensor pointwiseTensorPost tensorFreeZeroPointwiseIso)

open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.PointedSimplicialSet

/-- 基点付き写像対象の値域スペクトルに関する関手。 -/
def pointedMappingSpaceFunctor (E : SymmetricSpectrum.{u}) :
    SymmetricSpectrum.{u} ⥤ PointedSimplicialSet.{u} :=
  ihom E ⋙ evaluation 0

/-- 基点付き写像対象は内部Homスペクトルの第0段。 -/
def pointedMappingSpace (E F : SymmetricSpectrum.{u}) : PointedSimplicialSet.{u} :=
  RepresentedMappingEnrichment.hom pointedMappingSpaceFunctor.{u} E F

/-- 基点付き写像対象は原変数に反変、値域に共変な二変数関手。 -/
def pointedMappingSpaceBifunctor : SymmetricSpectrum.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ PointedSimplicialSet.{u} :=
  MonoidalClosed.internalHom (C := SymmetricSpectrum.{u}) ⋙
    (CategoryTheory.Functor.whiskeringRight _ _ _).obj (evaluation 0)

/-- 二変数関手の対象は構成済みの基点付き写像対象。 -/
lemma pointedMappingSpaceBifunctor_obj (E F : SymmetricSpectrum.{u}) :
    (pointedMappingSpaceBifunctor.obj (Opposite.op E)).obj F = pointedMappingSpace E F := rfl

/-- 固定したスペクトルに基点付き単体的集合をテンソルする関手。 -/
def mappingTensorFunctor (E : SymmetricSpectrum.{u}) :
    PointedSimplicialSet.{u} ⥤ SymmetricSpectrum.{u} :=
  MappingUnitLaws.parameterFunctor pointwiseTensorBifunctor.{u} E

/-- 第0段の自由生成との比較は生成対象に関する自然同型。 -/
def mappingTensorNatIso (E : SymmetricSpectrum.{u}) :
    (freeAt 0) ⋙ tensorRight E ≅ mappingTensorFunctor E :=
  FunctorTransport.iso ((freeAt 0) ⋙ tensorRight E)
    (fun X => pointwiseTensor X E) (fun X => tensorFreeZeroPointwiseIso X E)

/-- パラメータ関手の射は既存の生成対象のテンソル射。 -/
lemma mappingTensorFunctor_map {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    (E : SymmetricSpectrum.{u}) : (mappingTensorFunctor E).map f = pointwiseTensorPost f E :=
  rfl

/-- 各段のsmashと写像対象の、スペクトル変数に関して自然な随伴。 -/
def pointedMappingSpaceParametrizedAdjunction :
    pointwiseTensorBifunctor.{u}.flip ⊣₂ pointedMappingSpaceBifunctor.{u} :=
  MonoidalMappingAdjunction.transportedParametrizedAdjunction (freeAtAdjunction.{u} 0)
    pointwiseTensorBifunctor.{u} mappingTensorNatIso
    (fun {_ _} f X ↦ (sphereTensorFreeZeroPointwiseNatIso X).hom.naturality f)

/-- 各段のsmashと基点付き写像対象の随伴。 -/
def pointedMappingSpaceAdjunction (E : SymmetricSpectrum.{u}) :
    mappingTensorFunctor E ⊣ pointedMappingSpaceFunctor E :=
  pointedMappingSpaceParametrizedAdjunction.adj E

/-- 各段のsmashからの射と写像対象への基点付き射の自然なHom同値。 -/
def pointedMappingSpaceHomEquiv (X : PointedSimplicialSet.{u}) (E F : SymmetricSpectrum.{u}) :
    (pointwiseTensor X E ⟶ F) ≃ (X ⟶ pointedMappingSpace E F) :=
  (pointedMappingSpaceAdjunction E).homEquiv X F

/-- 写像対象への転置。 -/
def mappingSpaceCurry (X : PointedSimplicialSet.{u}) {E F : SymmetricSpectrum.{u}}
    (f : pointwiseTensor X E ⟶ F) : X ⟶ pointedMappingSpace E F :=
  pointedMappingSpaceHomEquiv X E F f

/-- 写像対象からの逆転置。 -/
def mappingSpaceUncurry (X : PointedSimplicialSet.{u}) {E F : SymmetricSpectrum.{u}}
    (f : X ⟶ pointedMappingSpace E F) : pointwiseTensor X E ⟶ F :=
  (pointedMappingSpaceHomEquiv X E F).symm f

/-- 写像対象の転置の左相互逆性の法則。 -/
def mappingSpaceUncurryCurryLaw (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : pointwiseTensor X E ⟶ F) : Prop :=
  AdjunctionHomLaws.uncurryCurryLaw (pointedMappingSpaceAdjunction E) f

/-- 写像対象の転置の右相互逆性の法則。 -/
def mappingSpaceCurryUncurryLaw (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : X ⟶ pointedMappingSpace E F) : Prop :=
  AdjunctionHomLaws.curryUncurryLaw (pointedMappingSpaceAdjunction E) f

/-- 転置して逆転置すると元の射になる。 -/
lemma mappingSpaceUncurry_curry (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : pointwiseTensor X E ⟶ F) :
    mappingSpaceUncurryCurryLaw X f :=
  AdjunctionHomLaws.uncurry_curry (pointedMappingSpaceAdjunction E) f

/-- 逆転置して転置すると元の射になる。 -/
lemma mappingSpaceCurry_uncurry (X : PointedSimplicialSet.{u})
    {E F : SymmetricSpectrum.{u}} (f : X ⟶ pointedMappingSpace E F) :
    mappingSpaceCurryUncurryLaw X f :=
  AdjunctionHomLaws.curry_uncurry (pointedMappingSpaceAdjunction E) f

/-- 写像対象の転置の値域に関する自然性の法則。 -/
def mappingSpaceCurryNaturalityRightLaw (X : PointedSimplicialSet.{u})
    {E F G : SymmetricSpectrum.{u}} (f : pointwiseTensor X E ⟶ F) (g : F ⟶ G) : Prop :=
  AdjunctionHomLaws.curryNaturalityRightLaw (pointedMappingSpaceAdjunction E) f g

/-- 転置は値域スペクトルの射に関して自然。 -/
lemma mappingSpaceCurry_naturality_right (X : PointedSimplicialSet.{u})
    {E F G : SymmetricSpectrum.{u}} (f : pointwiseTensor X E ⟶ F) (g : F ⟶ G) :
    mappingSpaceCurryNaturalityRightLaw X f g :=
  AdjunctionHomLaws.curry_naturality_right (pointedMappingSpaceAdjunction E) f g

/-- 転置はパラメータの基点付き単体的集合に関して自然。 -/
def mappingSpaceCurryNaturalityLeftLaw {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : pointwiseTensor Y E ⟶ F) : Prop :=
  AdjunctionHomLaws.curryNaturalityLeftLaw (pointedMappingSpaceAdjunction E) f g

/-- 転置はパラメータの基点付き単体的集合に関して自然。 -/
lemma mappingSpaceCurry_naturality_left {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y)
    {E F : SymmetricSpectrum.{u}} (g : pointwiseTensor Y E ⟶ F) :
    mappingSpaceCurryNaturalityLeftLaw f g :=
  AdjunctionHomLaws.curry_naturality_left (pointedMappingSpaceAdjunction E) f g

/-- 基点付き写像対象の評価。 -/
def mappingSpaceEvaluation (E F : SymmetricSpectrum.{u}) :
    pointwiseTensor (pointedMappingSpace E F) E ⟶ F :=
  RepresentedMappingEnrichment.evaluation pointwiseTensorBifunctor.{u}
    pointedMappingSpaceFunctor.{u} pointedMappingSpaceAdjunction.{u} E F

end SerrePositivity.SymmetricSpectrum
