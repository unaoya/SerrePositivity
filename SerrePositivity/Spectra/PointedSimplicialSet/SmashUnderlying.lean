module

public import SerrePositivity.Spectra.PointedSimplicialSet.Monoidal

/-! # 基点を忘れたsmashの標準射と零次単体 -/

@[expose] public section

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped Simplicial

/-- 基点を忘れた二つの対象の直積からsmashの基礎単体的集合への標準射。 -/
def productToSmash (X Y : PointedSimplicialSet.{u}) :
    X.right ⊗ Y.right ⟶ (X ⊗ Y).right := (PointedObject.smashQuotient X Y).right

/-- 標準射は基点を保つ両変数の射に関して自然。 -/
lemma productToSmash_naturality {X X' Y Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f.right ⊗ₘ g.right) ≫ productToSmash X' Y' =
      productToSmash X Y ≫ (f ⊗ₘ g).right :=
  (congrArg (fun k => k.right) (PointedObject.smashQuotient_map f g)).symm

/-- 零次球面からの基点付き射と基礎単体的集合の零次単体の同値。 -/
def unitVertexEquiv (X : PointedSimplicialSet.{u}) :
    (𝟙_ PointedSimplicialSet.{u} ⟶ X) ≃ X.right _⦋0⦌ :=
  (PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) X).trans X.right.unitHomEquiv

/-- 零次単体の同値は値域の基点付き射に関して自然。 -/
lemma unitVertexEquiv_naturality {X Y : PointedSimplicialSet.{u}}
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) (g : X ⟶ Y) :
    unitVertexEquiv Y (f ≫ g) = g.right.app (Opposite.op ⦋0⦌) (unitVertexEquiv X f) := by
  have h := (PointedObject.adjoinForgetAdjunction (C := SSet.{u})).homEquiv_naturality_right f g
  change PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) Y (f ≫ g) =
    PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) X f ≫ g.right at h
  exact congrArg (fun k => Y.right.unitHomEquiv k) h

/-- 零次球面からの基点付き射を、非基点側の点として通常の単体写像へ送る。 -/
def unitUnderlyingHom (X : PointedSimplicialSet.{u})
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) : 𝟙_ SSet.{u} ⟶ X.right :=
  PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) X f

/-- 通常の単体写像の零次単体は、零次球面からの射の同値で得る点。 -/
lemma unitUnderlyingHom_vertex (X : PointedSimplicialSet.{u})
    (f : 𝟙_ PointedSimplicialSet.{u} ⟶ X) :
    X.right.unitHomEquiv (unitUnderlyingHom X f) = unitVertexEquiv X f := rfl

end SerrePositivity.PointedSimplicialSet
