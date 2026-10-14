module

public import SerrePositivity.Spectra.SymmetricSpectrum.MappingSpaceArrowComposition
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
  PointedSimplicialSet.forget.obj (pointedMappingSpace E F)

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
    PointedSimplicialSet.productToSmash (pointedMappingSpace F G) (pointedMappingSpace E F) ≫
      PointedSimplicialSet.forget.map (mappingSpaceComposition E F G)

/-- 写像対象の単位の非基点側を選んだ通常の単体写像。 -/
def simplicialMappingUnit (E : SymmetricSpectrum.{u}) :
    𝟙_ SSet.{u} ⟶ simplicialMappingSpace E E :=
  PointedSimplicialSet.unitUnderlyingHom (pointedMappingSpace E E) (mappingSpaceUnit E)

/-- 通常のスペクトル射と単体的写像対象の零次単体の同値。 -/
def simplicialMappingVertexEquiv (E F : SymmetricSpectrum.{u}) :
    (E ⟶ F) ≃ (simplicialMappingSpace E F) _⦋0⦌ :=
  (mappingSpaceArrowEquiv E F).trans
    (PointedSimplicialSet.unitVertexEquiv (pointedMappingSpace E F))

/-- 通常の単体写像の単位の零次単体は、基点付き写像対象の単位の点。 -/
lemma simplicialMappingUnit_vertex (E : SymmetricSpectrum.{u}) :
    (simplicialMappingSpace E E).unitHomEquiv (simplicialMappingUnit E) =
      PointedSimplicialSet.unitVertexEquiv (pointedMappingSpace E E) (mappingSpaceUnit E) :=
  PointedSimplicialSet.unitUnderlyingHom_vertex (pointedMappingSpace E E) (mappingSpaceUnit E)

end SerrePositivity.SymmetricSpectrum
