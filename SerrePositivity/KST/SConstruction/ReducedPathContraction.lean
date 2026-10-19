module
public import SerrePositivity.KST.SConstruction.PathContractionSection
public import SerrePositivity.KST.SConstruction.RawCofiberCylinderDesc
public import SerrePositivity.KST.SConstruction.ReducedPathDiagonal

/-! # 元の点つき経路商の基点固定収縮
概要：既存の経路収縮を元の定数経路の cofiber 商へ降ろし、基点固定と両端を示す。
方針：切断の区間全体での固定を通常の cofiber cylinder の降下に渡す。
規約：Kan 置換前の元の点つき経路商。使われ方：零行の loop 射と既存 fiber 比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 定数切断の cylinder は、元の収縮と商射の合成で厳密に基点へ写る。 -/
lemma simplicialPathDiagonalCylinder_section_quotient (D : SimplicialObject SSet.{u}) :
    (simplicialPathDiagonalSection D ▷ (Δ[1] : SSet.{u})) ≫
        simplicialPathDiagonalCylinder D ≫ pathDiagonalReductionQuotient D =
      toUnit (D.obj (Opposite.op ⦋0⦌) ⊗ (Δ[1] : SSet.{u})) ≫ (reducedPathDiagonal D).hom := by
  rw [← Category.assoc, simplicialPathDiagonalCylinder_section, Category.assoc]
  change _ ≫ (simplicialPathDiagonalSection D ≫
    PointedObject.cofiberQuotient (simplicialPathDiagonalSection D)) = _
  rw [PointedObject.cofiberQuotient_condition, comp_toUnit_assoc]
  rfl

/-- 元の点つき経路商に降ろした、基点を区間全体で固定する収縮の cylinder。 -/
def reducedPathDiagonalCylinder (D : SimplicialObject SSet.{u}) :
    (reducedPathDiagonal D).right ⊗ (Δ[1] : SSet.{u}) ⟶ (reducedPathDiagonal D).right :=
  rawCofiberCylinderDesc (simplicialPathDiagonalSection D) (Δ[1] : SSet.{u})
    (reducedPathDiagonal D)
    (simplicialPathDiagonalCylinder D ≫ pathDiagonalReductionQuotient D)
    (simplicialPathDiagonalCylinder_section_quotient D)

/-- 元の商射で引き戻すと元の収縮の cylinder を厳密に回収する。 -/
lemma reducedPathDiagonalCylinder_quotient (D : SimplicialObject SSet.{u}) :
    (pathDiagonalReductionQuotient D ▷ (Δ[1] : SSet.{u})) ≫ reducedPathDiagonalCylinder D =
      simplicialPathDiagonalCylinder D ≫ pathDiagonalReductionQuotient D :=
  rawCofiberCylinderDesc_quotient _ _ _ _ _

/-- 降ろした収縮は元の点つき経路商の基点を区間全体で固定する。 -/
lemma reducedPathDiagonalCylinder_point (D : SimplicialObject SSet.{u}) :
    ((reducedPathDiagonal D).hom ▷ (Δ[1] : SSet.{u})) ≫ reducedPathDiagonalCylinder D =
      toUnit ((𝟙_ SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ (reducedPathDiagonal D).hom :=
  rawCofiberCylinderDesc_point _ _ _ _ _

/-- 元の点つき経路商の収縮の始点は基点への定数写像。 -/
lemma reducedPathDiagonalCylinder_zero (D : SimplicialObject SSet.{u}) :
    SSet.ι₀ ≫ reducedPathDiagonalCylinder D =
      toUnit (reducedPathDiagonal D).right ≫ (reducedPathDiagonal D).hom := by
  apply (IsPushout.of_hasPushout (simplicialPathDiagonalSection D)
    (toUnit (D.obj (Opposite.op ⦋0⦌)))).hom_ext
  · change pathDiagonalReductionQuotient D ≫
      (SSet.ι₀ ≫ reducedPathDiagonalCylinder D) =
        pathDiagonalReductionQuotient D ≫
          (toUnit (reducedPathDiagonal D).right ≫ (reducedPathDiagonal D).hom)
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc,
      reducedPathDiagonalCylinder_quotient, ← Category.assoc,
      simplicialPathDiagonalCylinder_zero, Category.assoc]
    change simplicialPathDiagonalProjection D ≫ (simplicialPathDiagonalSection D ≫
      PointedObject.cofiberQuotient (simplicialPathDiagonalSection D)) = _
    rw [PointedObject.cofiberQuotient_condition]
    change simplicialPathDiagonalProjection D ≫
      (toUnit (D.obj (Opposite.op ⦋0⦌)) ≫ (reducedPathDiagonal D).hom) = _
    simp only [comp_toUnit_assoc]
  · change (reducedPathDiagonal D).hom ≫ (SSet.ι₀ ≫ reducedPathDiagonalCylinder D) =
      (reducedPathDiagonal D).hom ≫
        (toUnit (reducedPathDiagonal D).right ≫ (reducedPathDiagonal D).hom)
    rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, reducedPathDiagonalCylinder_point]
    simp only [comp_toUnit_assoc]

/-- 元の点つき経路商の収縮の終点は恒等射。 -/
lemma reducedPathDiagonalCylinder_one (D : SimplicialObject SSet.{u}) :
    SSet.ι₁ ≫ reducedPathDiagonalCylinder D = 𝟙 _ := by
  apply (IsPushout.of_hasPushout (simplicialPathDiagonalSection D)
    (toUnit (D.obj (Opposite.op ⦋0⦌)))).hom_ext
  · change pathDiagonalReductionQuotient D ≫
      (SSet.ι₁ ≫ reducedPathDiagonalCylinder D) =
        pathDiagonalReductionQuotient D ≫ 𝟙 (reducedPathDiagonal D).right
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc,
      reducedPathDiagonalCylinder_quotient, ← Category.assoc,
      simplicialPathDiagonalCylinder_one, Category.id_comp, Category.comp_id]
  · change (reducedPathDiagonal D).hom ≫ (SSet.ι₁ ≫ reducedPathDiagonalCylinder D) =
      (reducedPathDiagonal D).hom ≫ 𝟙 (reducedPathDiagonal D).right
    rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, reducedPathDiagonalCylinder_point]
    simp only [comp_toUnit_assoc, toUnit_unit, Category.id_comp, Category.comp_id]

/-- 元の点つき経路商の、基点定数写像から恒等射への実際の収縮ホモトピー。 -/
def reducedPathDiagonalContraction (D : SimplicialObject SSet.{u}) :
    SSet.Homotopy (toUnit (reducedPathDiagonal D).right ≫ (reducedPathDiagonal D).hom)
      (𝟙 (reducedPathDiagonal D).right) where
  h := reducedPathDiagonalCylinder D
  h₀ := reducedPathDiagonalCylinder_zero D
  h₁ := reducedPathDiagonalCylinder_one D
  rel := by ext n ⟨⟨x, hx⟩, t⟩; exact hx.elim

end SerrePositivity.KST.SConstruction
