module
public import SerrePositivity.KST.SConstruction.ZeroRowContractionDegeneracy
public import SerrePositivity.KST.SConstruction.LoopCylinderConstantParameter

/-! # 元の零行収縮の境界像による具体的な loop 比較
概要：零行収縮を既存の Kan 境界へ写した区間族を、既存の loop 空間へ厳密に降ろす。
方針：収縮の両端と零行の厳密な零境界を使い、円の商と点つき curry を適用する。
規約：元の区間の向きを保つ。使われ方：元の構造射の随伴と fiber 比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- 元の零行収縮の既存の Kan 境界での像。 -/
def zeroRowBoundaryCylinder (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⊗ (Δ[1] : SSet.{u}) ⟶
      ((boundaryKanRealizationFunctor r).obj X).right :=
  zeroRowPathContraction r X ≫ (pointedFullIteratedPathKanBoundary r X).right

/-- 元の零行の境界の区間族の始点は厳密に基点。 -/
lemma zeroRowBoundaryCylinder_zero (r : ℕ) (X : StableModel.{u}) :
    SSet.ι₀ ≫ zeroRowBoundaryCylinder r X =
      toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((boundaryKanRealizationFunctor r).obj X).hom := by
  change SSet.ι₀ ≫ zeroRowPathContraction r X ≫ _ = _
  rw [← Category.assoc, zeroRowPathContraction_zero, Category.assoc, Under.w]

/-- 元の零行の境界の区間族の終点も厳密に基点。 -/
lemma zeroRowBoundaryCylinder_one (r : ℕ) (X : StableModel.{u}) :
    SSet.ι₁ ≫ zeroRowBoundaryCylinder r X =
      toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((boundaryKanRealizationFunctor r).obj X).hom := by
  change SSet.ι₁ ≫ zeroRowPathContraction r X ≫ _ = _
  rw [← Category.assoc, zeroRowPathContraction_one, zeroRowPathToKan_boundary]

/-- 元の零行から既存の Kan 実現の loop 空間への具体的な比較。 -/
def zeroRowLoopComparison (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X)).right :=
  loopOfCylinder ((boundaryKanRealizationFunctor r).obj X) (zeroRowBoundaryCylinder r X)
    (zeroRowBoundaryCylinder_zero r X) (zeroRowBoundaryCylinder_one r X)

/-- 元の零段の退化像は区間全体で Kan 境界の基点に留まる。 -/
lemma zeroRowBoundaryCylinder_degeneracy (r : ℕ) (X : StableModel.{u}) :
    ((iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ▷
        (Δ[1] : SSet.{u})) ≫ zeroRowBoundaryCylinder r X =
      toUnit (((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ⊗
        (Δ[1] : SSet.{u})) ≫ ((boundaryKanRealizationFunctor r).obj X).hom := by
  change _ ≫ zeroRowPathContraction r X ≫ (pointedFullIteratedPathKanBoundary r X).right = _
  rw [← Category.assoc, zeroRowPathContraction_degeneracy, Category.assoc, Under.w]

/-- 元の零段の退化像は構成した loop 射で定数 loop に厳密に写る。 -/
lemma zeroRowLoopComparison_degeneracy (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
        zeroRowLoopComparison r X =
      toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace ((boundaryKanRealizationFunctor r).obj X)).hom :=
  loopOfCylinder_constant_parameter _ _ _ _ _ (zeroRowBoundaryCylinder_degeneracy r X)

/-- 円の商射と通常の評価は、元の向きの零行収縮の境界像を回収する。 -/
lemma zeroRowLoopComparison_raw (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
      MonoidalClosed.uncurry (zeroRowLoopComparison r X ≫
        PointedObject.basedHomι PointedSimplicialSet.circle.{u}
          ((boundaryKanRealizationFunctor r).obj X)) =
      (β_ (Δ[1] : SSet.{u})
        ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌))).hom ≫
          zeroRowBoundaryCylinder r X :=
  loopOfCylinder_raw _ _ _ _

/-- 構成した loop 比較の評価は元の一次段の区間組み立てそのもの。 -/
lemma zeroRowLoopComparison_assembly (r : ℕ) (X : StableModel.{u}) :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ▷
      (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
      MonoidalClosed.uncurry (zeroRowLoopComparison r X ≫
        PointedObject.basedHomι PointedSimplicialSet.circle.{u}
          ((boundaryKanRealizationFunctor r).obj X)) =
      diagonalAssembly 1 (iteratedSRealizationDiagram r X) ≫ iteratedRealizationToKan r X := by
  rw [zeroRowLoopComparison_raw]
  change _ ≫ zeroRowPathContraction r X ≫ (pointedFullIteratedPathKanBoundary r X).right = _
  rw [zeroRowPathContraction_boundary, ← Category.assoc, SymmetricCategory.symmetry]
  rfl

end SerrePositivity.KST.SConstruction
