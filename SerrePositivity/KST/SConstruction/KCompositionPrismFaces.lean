module
public import SerrePositivity.KST.SConstruction.TrianglePrismMappingSquares
public import SerrePositivity.KST.SConstruction.KSuspensionMappingTriangles

/-! # 元の K の合成 prism の六つの指定三角形
概要：元の合成二単体 prism の三つの三単体と、前後・合成射の既存三角形を厳密に照合する。
方針：同じ元の prism の面自然性と階段状三単体の指定面を使う。
規約：零段を含み、元の三角形・対角辺を選び直さない。
使われ方：三つの Hom 正方形の外側境界を、元の適合区間へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPrismFacesPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の二本の入力射の合成二単体に制限した同じ K prism。 -/
def kKanOriginalCompositionPrism := kKanOriginalSuspensionPrism r F (ComposableArrows.mk₂ f g)

/-- 元の合成 prism の三つの coherent 三単体像。 -/
def kKanOriginalCompositionImage (q : Fin 3) :=
  trianglePrismImage (kKanOriginalCompositionPrism r F f g) q

/-- 元の合成 prism の前の射の側面は、同じ元の自然性 square。 -/
lemma kKanOriginalCompositionPrism_first :
    (SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      kKanOriginalCompositionPrism r F f g = kKanOriginalSuspensionSquare r F f := by
  have h := kKanOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (2 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g =
      kKanOriginalSuspensionPrism r F ((nerve I).δ 2 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₂_mk₂_eq] at h
  exact h

/-- 元の合成 prism の後続射の側面は、同じ元の自然性 square。 -/
lemma kKanOriginalCompositionPrism_second :
    (SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      kKanOriginalCompositionPrism r F f g = kKanOriginalSuspensionSquare r F g := by
  have h := kKanOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (0 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g =
      kKanOriginalSuspensionPrism r F ((nerve I).δ 0 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₀_mk₂_eq] at h
  exact h

/-- 元の合成 prism の合成射の側面は、同じ元の自然性 square。 -/
lemma kKanOriginalCompositionPrism_composite :
    (SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
      kKanOriginalCompositionPrism r F f g = kKanOriginalSuspensionSquare r F (f ≫ g) := by
  have h := kKanOriginalSuspensionPrism_naturality r F
    (SimplexCategory.δ (1 : Fin 3)) (ComposableArrows.mk₂ f g)
  change (SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g =
      kKanOriginalSuspensionPrism r F ((nerve I).δ 1 (ComposableArrows.mk₂ f g)) at h
  rw [nerve.δ₁_mk₂_eq] at h
  exact h

/-- 指定した元の合成射の上側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_composite_upper :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 2
      (kKanOriginalCompositionImage r F f g 0) =
        (kKanSuspensionMappingTriangles r F (f ≫ g)).leftTop.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_composite_upper
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_composite]
  rfl

/-- 指定した元の合成射の下側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_composite_lower :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 1
      (kKanOriginalCompositionImage r F f g 2) =
        (kKanSuspensionMappingTriangles r F (f ≫ g)).bottomRight.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_composite_lower
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_composite]
  rfl

/-- 指定した元の前の射の上側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_first_upper :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 3
      (kKanOriginalCompositionImage r F f g 0) =
        (kKanSuspensionMappingTriangles r F f).leftTop.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_first_upper
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_first]
  rfl

/-- 指定した元の前の射の下側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_first_lower :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 3
      (kKanOriginalCompositionImage r F f g 1) =
        (kKanSuspensionMappingTriangles r F f).bottomRight.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_first_lower
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (2 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_first]
  rfl

/-- 指定した元の後続射の上側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_second_upper :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 0
      (kKanOriginalCompositionImage r F f g 1) =
        (kKanSuspensionMappingTriangles r F g).leftTop.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_second_upper
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_second]
  rfl

/-- 指定した元の後続射の下側面は、既存の同じ square の実三角形。 -/
lemma kKanOriginalCompositionImage_second_lower :
    (SimplicialNerve PointedSimplicialSet.{u}).δ 0
      (kKanOriginalCompositionImage r F f g 2) =
        (kKanSuspensionMappingTriangles r F g).bottomRight.simplex := by
  have h := trianglePrismImage_face (kKanOriginalCompositionPrism r F f g)
    trianglePrismTetrahedron_second_lower
  refine h.trans ?_
  change ((SSet.stdSimplex.δ (0 : Fin 3) ▷ (Δ[1] : SSet.{u + 1})) ≫
    kKanOriginalCompositionPrism r F f g).app (Opposite.op ⦋2⦌) _ = _
  rw [kKanOriginalCompositionPrism_second]
  rfl

end SerrePositivity.KST.SConstruction
