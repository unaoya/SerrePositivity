module
public import SerrePositivity.KST.SConstruction.PointedTensorEnrichedFunctor
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint

/-! # 自由点つき区間との元の smash による関手的円柱
概要：点つき区間を左に smash し、元の二つの端点と射影を保持する。
方針：端点と終射の自由基点追加を使い、左単位同型で同じ元の対象へ戻す。
規約：全て同じ元の smash 商の射。使われ方：関手的 BF 単射置換。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 元の標準区間に、別の基点を自由に追加した点つき区間。 -/
def pointedTensorInterval : PointedSimplicialSet.{u} :=
  PointedObject.adjoin (Δ[1] : SSet.{u})

/-- 零次球面からの、元の区間の指定端点の自由点つき射。 -/
def pointedTensorIntervalEnd (i : Fin 2) :
    (𝟙_ PointedSimplicialSet.{u}) ⟶ pointedTensorInterval.{u} :=
  PointedObject.adjoinFunctor.map
    (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm i))

/-- 元の区間の終射からの、零次球面への自由点つき射。 -/
def pointedTensorIntervalProjection :
    pointedTensorInterval.{u} ⟶ (𝟙_ PointedSimplicialSet.{u}) :=
  PointedObject.adjoinFunctor.map (toUnit (Δ[1] : SSet.{u}))

/-- 両端は、同じ元の零次球面上の射影の切断。 -/
lemma pointedTensorIntervalEnd_projection (i : Fin 2) :
    pointedTensorIntervalEnd.{u} i ≫ pointedTensorIntervalProjection = 𝟙 _ := by
  change PointedObject.adjoinFunctor.map _ ≫ PointedObject.adjoinFunctor.map _ = _
  rw [← Functor.map_comp]
  have h : (SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm i)) ≫
      toUnit (Δ[1] : SSet.{u}) = 𝟙 _ := Subsingleton.elim _ _
  rw [h]
  exact PointedObject.adjoinFunctor.map_id _

/-- 元の自由点つき区間を左に smash する厳密単体的豊穣円柱関手。 -/
def pointedTensorCylinderFunctor :
    EnrichedFunctor SSet.{u} PointedSSetObject.{u} PointedSSetObject.{u} :=
  pointedTensorEnrichedFunctor pointedTensorInterval

/-- 同じ元の端点射を、基礎点つき圏の型で保持する。 -/
def pointedTensorCylinderEndMap (i : Fin 2) (X : PointedSimplicialSet.{u}) :
    X ⟶ pointedTensorInterval.{u} ⊗ X :=
  (λ_ X).inv ≫ pointedTensorIntervalEnd i ▷ X

/-- 同じ元の射影を、基礎点つき圏の型で保持する。 -/
def pointedTensorCylinderProjectionMap (X : PointedSimplicialSet.{u}) :
    pointedTensorInterval.{u} ⊗ X ⟶ X :=
  pointedTensorIntervalProjection ▷ X ≫ (λ_ X).hom

/-- 基礎点つき圏でも、元の両端は同じ元の射影の切断。 -/
lemma pointedTensorCylinderEndMap_projection (i : Fin 2) (X : PointedSimplicialSet.{u}) :
    pointedTensorCylinderEndMap i X ≫ pointedTensorCylinderProjectionMap X = 𝟙 X := by
  change ((λ_ X).inv ≫ pointedTensorIntervalEnd i ▷ X) ≫
    (pointedTensorIntervalProjection ▷ X ≫ (λ_ X).hom) = 𝟙 X
  rw [Category.assoc, ← Category.assoc (pointedTensorIntervalEnd i ▷ X),
    ← comp_whiskerRight, pointedTensorIntervalEnd_projection, id_whiskerRight]
  exact (λ_ X).inv_hom_id

/-- 円柱の指定端点は、元の端点射と逆左単位子からなる。 -/
def pointedTensorCylinderEnd (i : Fin 2) (X : PointedSSetObject.{u}) :
    X ⟶ pointedTensorCylinderFunctor.obj X :=
  pointedTensorCylinderEndMap i X.obj

/-- 円柱の射影は、元の区間の終射と左単位子からなる。 -/
def pointedTensorCylinderProjection (X : PointedSSetObject.{u}) :
    pointedTensorCylinderFunctor.obj X ⟶ X :=
  pointedTensorCylinderProjectionMap X.obj

/-- 元の円柱の両端は、それぞれ同じ元の射影の切断。 -/
lemma pointedTensorCylinderEnd_projection (i : Fin 2) (X : PointedSSetObject.{u}) :
    pointedTensorCylinderEnd i X ≫ pointedTensorCylinderProjection X = 𝟙 X :=
  pointedTensorCylinderEndMap_projection i X.obj

/-- 元の基礎単体集合上でも、指定端点の射は分裂単射。 -/
instance pointedTensorCylinderEnd_isSplitMono (i : Fin 2) (X : PointedSSetObject.{u}) :
    IsSplitMono (pointedTensorCylinderEnd i X).right :=
  IsSplitMono.mk' ⟨(pointedTensorCylinderProjection X).right,
    congrArg Under.Hom.right (pointedTensorCylinderEnd_projection i X)⟩

end SerrePositivity.KST.SConstruction
