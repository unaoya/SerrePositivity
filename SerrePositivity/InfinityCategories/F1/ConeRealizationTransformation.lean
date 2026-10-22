module

public import SerrePositivity.InfinityCategories.F1.ConeTransformationPointAt
public import SerrePositivity.InfinityCategories.F1.SourceConstantTransformationVertex
public import SerrePositivity.InfinityCategories.F1.SourceConstantTransformationHomotopy
public import SerrePositivity.InfinityCategories.F1.HomotopyConeBoundary
public import SerrePositivity.InfinityCategories.F1.FatConeCylinderIso

/-!
概要：指定変換から実現した錐の標準変換を、同じ元の指定変換へ戻す。
方針：実現の両端固定比較を元の円柱で制限して curry する。
規約：元の錐・図式・指定頂点・比較時間全体を保持する。
使われ方：全切断の恒等射を表す変換との整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 実現した錐の標準変換と、元の指定変換の実際のホモトピー。 -/
def coneRealizationTransformationHomotopy
    (t : (intervalMappingSpace (functorVertex (SSet.const z)) (functorVertex f)) _⦋0⦌)
    (R : HomotopyConeRealization
      (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated)) :
    SSet.Homotopy (SSet.yonedaEquiv.symm (coneTransformationPointAt R.cone z R.vertex_eq))
      (SSet.yonedaEquiv.symm t) := by
  let a := SSet.yonedaEquiv.symm (coneTransformationPointAt R.cone z R.vertex_eq)
  let b := SSet.yonedaEquiv.symm t
  let q := fst (K ⊗ (Δ[1] : SSet.{u})) (Δ[0] : SSet.{u}) ≫ fatConeCylinderMap K
  let h := (q ▷ (Δ[1] : SSet.{u})) ≫ R.comparison.h
  have h₀ : SSet.ι₀ ≫ h = sourceConstantTransformationPrism a := by
    dsimp only [h]
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, R.comparison.h₀,
      coneTransformationPointAt_prism]
    rfl
  have h₁ : SSet.ι₁ ≫ h = sourceConstantTransformationPrism b := by
    dsimp only [h, q]
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, R.comparison.h₁,
      sourceConstantTransformationPrism_vertex, Category.assoc, fatConeCylinderMap,
      Category.assoc, homotopyFatCone_cylinder, ← Category.assoc]
    have hi : fatConeCylinderEmbedding K ≫ fatConeCylinderProjection K = 𝟙 _ :=
      (fatConeCylinderIso K).inv_hom_id
    rw [Category.assoc, ← Category.assoc (fatConeCylinderEmbedding K), hi, Category.id_comp]
  let H : SSet.Homotopy (sourceConstantTransformationPrism a)
      (sourceConstantTransformationPrism b) := ⟨h, h₀, h₁, by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property⟩
  apply sourceConstantTransformationHomotopyOfPrisms a b H
  · change ((SSet.ι₀ (X := K) ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ h = _
    dsimp only [h, q]
    rw [← Category.assoc, ← comp_whiskerRight]
    have he : (SSet.ι₀ (X := K) ▷ (Δ[0] : SSet.{u})) ≫
        (fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ fatConeCylinderMap K) =
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) : K ⊗ Δ[0] ⟶ Δ[0]) ≫
          fatJoinInl Δ[0] K := by
      change (fst K Δ[0] ≫ SSet.ι₀) ≫ fatConeCylinderMap K = _
      rw [Category.assoc, fatConeCylinderMap_zero, ← Category.assoc, SSet.comp_const]
    rw [he, comp_whiskerRight, Category.assoc, homotopyConeRealization_left, SSet.comp_const]
  · change ((SSet.ι₁ (X := K) ▷ (Δ[0] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ h = _
    dsimp only [h, q]
    rw [← Category.assoc, ← comp_whiskerRight]
    have he : (SSet.ι₁ (X := K) ▷ (Δ[0] : SSet.{u})) ≫
        (fst (K ⊗ (Δ[1] : SSet.{u})) Δ[0] ≫ fatConeCylinderMap K) =
        fst K Δ[0] ≫ fatJoinInr Δ[0] K := by
      change (fst K Δ[0] ≫ SSet.ι₁) ≫ fatConeCylinderMap K = _
      rw [Category.assoc, fatConeCylinderMap_one]
    rw [he, comp_whiskerRight, Category.assoc, homotopyConeRealization_right,
      ← Category.assoc, whiskerRight_fst, Category.assoc]

end SerrePositivity.InfinityCategories
