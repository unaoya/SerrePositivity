module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpace
public import SerrePositivity.Spectra.General.MappingEnrichment
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying

/-! # 基点を忘れた単体的写像対象、合成、単位、零次単体 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSpectrum

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped Simplicial

/-- 基点を忘れた通常の単体的写像対象。 -/
def simplicialMappingSpace (E F : SymmetricSpectrum.{u}) : SSet.{u} :=
  PointedSimplicialSet.forget.obj (GeneralSymmetricSpectrum.mappingObject E F)

/-- 通常の単体的写像対象の反変・共変の二変数関手。 -/
def simplicialMappingSpaceBifunctor : SymmetricSpectrum.{u}ᵒᵖ ⥤
    SymmetricSpectrum.{u} ⥤ SSet.{u} :=
  pointedMappingSpaceBifunctor ⋙
    (CategoryTheory.Functor.whiskeringRight _ _ _).obj PointedSimplicialSet.forget

/-- 二変数関手の対象は基点を忘れた写像対象。 -/
lemma simplicialMappingSpaceBifunctor_obj (E F : SymmetricSpectrum.{u}) :
    (simplicialMappingSpaceBifunctor.obj (Opposite.op E)).obj F =
      simplicialMappingSpace E F := rfl

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

end SerrePositivity.SymmetricSpectrum
