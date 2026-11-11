module
public import SerrePositivity.KST.SConstruction.LoopCylinderBoundary
public import SerrePositivity.KST.SConstruction.RawCofiberCylinderDesc
public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.KST.Spectra.SuspensionLoop

/-! # 両端が基点の区間族から既存の loop 空間への射
概要：通常の区間族を元の円の商へ降ろし、既存の点つき内部 Hom の loop に curry する。
方針：区間の境界の零化、通常の cofiber cylinder の降下、点つき写像族の curry を合成する。
規約：区間の向きを変更しない。使われ方：元の零行収縮の境界像からの具体的な loop 射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 両端が基点の区間族を、元の円と元のパラメータの通常の積へ降ろす。 -/
def circleCylinderDesc {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₀ : SSet.ι₀ ≫ h = toUnit A ≫ B.hom)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) :
    PointedSimplicialSet.circle.{u}.right ⊗ A ⟶ B.right :=
  rawCofiberCylinderDesc (boundary.{u} 1).ι A B ((β_ (Δ[1] : SSet.{u}) A).hom ≫ h) (by
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
      cylinder_boundary_constant B h h₀ h₁, comp_toUnit_assoc])

/-- 元の円の商射で引き戻すと、元の向きの区間族を回収する。 -/
lemma circleCylinderDesc_quotient {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫ circleCylinderDesc B h h₀ h₁ =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ h :=
  rawCofiberCylinderDesc_quotient _ _ _ _ _

/-- 降ろした円の族は、円の基点上で厳密に基点へ写る。 -/
lemma circleCylinderDesc_point {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) :
    (PointedSimplicialSet.circle.{u}.hom ▷ A) ≫ circleCylinderDesc B h h₀ h₁ =
      toUnit ((𝟙_ SSet.{u}) ⊗ A) ≫ B.hom :=
  rawCofiberCylinderDesc_point _ _ _ _ _

/-- 両端が基点の元の区間族による、既存の loop 空間への具体的な射。 -/
def loopOfCylinder {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right)
    (h₀ : SSet.ι₀ ≫ h = toUnit A ≫ B.hom)
    (h₁ : SSet.ι₁ ≫ h = toUnit A ≫ B.hom) : A ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry PointedSimplicialSet.circle.{u} B
    (circleCylinderDesc B h h₀ h₁) (circleCylinderDesc_point B h h₀ h₁)

/-- loop 射の通常の uncurry は元の円への降下そのもの。 -/
lemma loopOfCylinder_uncurry {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) :
    MonoidalClosed.uncurry (loopOfCylinder B h h₀ h₁ ≫
      PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
        circleCylinderDesc B h h₀ h₁ := by
  rw [loopOfCylinder, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, MonoidalClosed.uncurry_curry]

/-- 元の円の商射と通常の評価で loop 射を元の区間族へ厳密に戻す。 -/
lemma loopOfCylinder_raw {A : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷ A) ≫
      MonoidalClosed.uncurry (loopOfCylinder B h h₀ h₁ ≫
        PointedObject.basedHomι PointedSimplicialSet.circle.{u} B) =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ h := by
  rw [loopOfCylinder_uncurry, circleCylinderDesc_quotient]

end SerrePositivity.KST.SConstruction
