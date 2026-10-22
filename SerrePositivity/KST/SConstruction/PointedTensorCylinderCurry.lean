module
public import SerrePositivity.KST.SConstruction.PointedTensorCylinder
public import SerrePositivity.KST.Spectra.PointedVertexComparison

/-! # 同じ実円柱の閉 curry と両端評価
概要：自由点つき区間との元の円柱を、同じ基点固定写像空間の区間族へ送る。
方針：同じ smash の交換で curry し、元の両端を単位子と交換子で照合する。
規約：Kan 性は不要。使われ方：BF 構造射の比較の実ホモトピー。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed BraidedCategory Limits SSet
open scoped Simplicial

/-- 同じ自由基点追加の Hom 同値は、元のパラメータの前合成と可換。 -/
lemma pointedAdjoinHomEquiv_pre {P Q : SSet.{u}} (q : Q ⟶ P)
    {Z : PointedSimplicialSet.{u}} (a : PointedObject.adjoin P ⟶ Z) :
    q ≫ PointedObject.adjoinHomEquiv P Z a =
      PointedObject.adjoinHomEquiv Q Z (PointedObject.adjoinFunctor.map q ≫ a) := by
  change q ≫ (coprod.inl ≫ a.right) =
    coprod.inl ≫ (coprod.map q (𝟙 (𝟙_ SSet.{u})) ≫ a.right)
  erw [coprod.inl_map_assoc]

/-- 同じ実円柱射を、元の区間から基点固定写像空間への全族にする。 -/
def pointedTensorCylinderFamily {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) :
    (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom X Y).right :=
  PointedObject.adjoinHomEquiv _ _ (curry ((β_ X pointedTensorInterval).hom ≫ h))

/-- 同じ閉 curry の指定端点は、元の円柱端点上の射の閉単位表示。 -/
lemma pointedTensorCylinderCurry_end {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) (i : Fin 2) :
    pointedTensorIntervalEnd i ≫ curry ((β_ X pointedTensorInterval).hom ≫ h) =
      curry' (pointedTensorCylinderEndMap i X ≫ h) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, curry', uncurry_curry]
  change X ◁ pointedTensorIntervalEnd i ≫ ((β_ X pointedTensorInterval).hom ≫ h) =
    (ρ_ X).hom ≫ ((λ_ X).inv ≫ pointedTensorIntervalEnd i ▷ X ≫ h)
  rw [← Category.assoc, braiding_naturality_right, Category.assoc]
  have hu : (β_ X (𝟙_ PointedSimplicialSet.{u})).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
    rw [← cancel_mono (λ_ X).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      braiding_leftUnitor]
  rw [hu]
  simp only [Category.assoc]

/-- 同じ区間族の時刻 i は、元の円柱端点上の射の元の単位族。 -/
lemma pointedTensorCylinderFamily_end {X Y : PointedSimplicialSet.{u}}
    (h : pointedTensorInterval.{u} ⊗ X ⟶ Y) (i : Fin 2) :
    SSet.const (X := 𝟙_ SSet.{u}) (stdSimplex.obj₀Equiv.symm i) ≫
        pointedTensorCylinderFamily h =
      PointedSimplicialSet.unitUnderlyingHom (PointedObject.basedHom X Y)
        (curry' (pointedTensorCylinderEndMap i X ≫ h)) := by
  rw [pointedTensorCylinderFamily]
  erw [pointedAdjoinHomEquiv_pre]
  change PointedObject.adjoinHomEquiv _ _
    (pointedTensorIntervalEnd i ≫ curry ((β_ X pointedTensorInterval).hom ≫ h)) = _
  erw [pointedTensorCylinderCurry_end]
  rfl

end SerrePositivity.KST.SConstruction
