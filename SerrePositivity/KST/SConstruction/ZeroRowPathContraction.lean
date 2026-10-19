module
public import SerrePositivity.KST.SConstruction.ReducedPathBasedContraction
public import SerrePositivity.KST.SConstruction.ZeroRowKanFiberSquare

/-! # 元の零行から既存の Kan 経路全空間への収縮
概要：元の点つき経路商の収縮を零行へ制限し、既存の Kan 単位で写す。
方針：商射・両端・境界を元の射へ戻す式で照合する。
規約：零行も Kan 経路模型も変更しない。使われ方：元の構造射の随伴と fiber 比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial

/-- 元の経路零行から元の定数切断の商への写像。 -/
def zeroRowPathToQuotient (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⟶
      (pointedIteratedPathRealization r X).right :=
  diagonalZeroColumn (iteratedPathRealizationDiagram r X) ≫ pointedIteratedPathQuotient r X

/-- 元の零行から既存の Kan 経路全空間への元の収縮の制限。 -/
def zeroRowPathContraction (r : ℕ) (X : StableModel.{u}) :
    (iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌) ⊗ (Δ[1] : SSet.{u}) ⟶
      ((pointedIteratedPathKanFunctor r).obj X).right :=
  (zeroRowPathToQuotient r X ▷ (Δ[1] : SSet.{u})) ≫
    reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫
      (PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right

/-- 零行上の収縮は、元の経路収縮と元の Kan 比較の合成そのもの。 -/
lemma zeroRowPathContraction_raw (r : ℕ) (X : StableModel.{u}) :
    zeroRowPathContraction r X =
      (diagonalZeroColumn (iteratedPathRealizationDiagram r X) ▷ (Δ[1] : SSet.{u})) ≫
        simplicialPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫
          iteratedPathToKan r X := by
  change ((diagonalZeroColumn _ ≫ pointedIteratedPathQuotient r X) ▷ (Δ[1] : SSet.{u})) ≫
    reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫ _ = _
  rw [comp_whiskerRight_assoc]
  have hq : (pointedIteratedPathQuotient r X ▷ (Δ[1] : SSet.{u})) ≫
      reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) =
    simplicialPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫
      pointedIteratedPathQuotient r X :=
    reducedPathDiagonalCylinder_quotient (iteratedSRealizationDiagram r X)
  rw [← Category.assoc (pointedIteratedPathQuotient r X ▷ _), hq]
  rfl

/-- 零行上の収縮の始点は既存の Kan 経路模型の基点に厳密に定数。 -/
lemma zeroRowPathContraction_zero (r : ℕ) (X : StableModel.{u}) :
    SSet.ι₀ ≫ zeroRowPathContraction r X =
      toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        ((pointedIteratedPathKanFunctor r).obj X).hom := by
  have he : (SSet.ι₀ : (pointedIteratedPathRealization r X).right ⟶
      (pointedIteratedPathRealization r X).right ⊗ (Δ[1] : SSet.{u})) ≫
      reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) =
    toUnit (pointedIteratedPathRealization r X).right ≫
      (pointedIteratedPathRealization r X).hom :=
    reducedPathDiagonalCylinder_zero (iteratedSRealizationDiagram r X)
  have hp : (pointedIteratedPathRealization r X).hom ≫
      (PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right =
    ((pointedIteratedPathKanFunctor r).obj X).hom := Under.w _
  change SSet.ι₀ ≫ (zeroRowPathToQuotient r X ▷ (Δ[1] : SSet.{u})) ≫
    reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫ _ = _
  rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, ← Category.assoc SSet.ι₀,
    he]
  simp only [Category.assoc, comp_toUnit_assoc, hp]

/-- 零行上の収縮の終点は元の零行から既存の Kan 経路への射を回収する。 -/
lemma zeroRowPathContraction_one (r : ℕ) (X : StableModel.{u}) :
    SSet.ι₁ ≫ zeroRowPathContraction r X = zeroRowPathToKan r X := by
  have he : (SSet.ι₁ : (pointedIteratedPathRealization r X).right ⟶
      (pointedIteratedPathRealization r X).right ⊗ (Δ[1] : SSet.{u})) ≫
      reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) =
    𝟙 (pointedIteratedPathRealization r X).right :=
    reducedPathDiagonalCylinder_one (iteratedSRealizationDiagram r X)
  change SSet.ι₁ ≫ (zeroRowPathToQuotient r X ▷ (Δ[1] : SSet.{u})) ≫
    reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫ _ = _
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, ← Category.assoc SSet.ι₁,
    he, Category.id_comp]
  rfl

/-- 元の零行の Kan 経路比較への実際の収縮ホモトピー。 -/
def zeroRowPathContractionHomotopy (r : ℕ) (X : StableModel.{u}) :
    SSet.Homotopy (toUnit ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
      ((pointedIteratedPathKanFunctor r).obj X).hom) (zeroRowPathToKan r X) where
  h := zeroRowPathContraction r X
  h₀ := zeroRowPathContraction_zero r X
  h₁ := zeroRowPathContraction_one r X
  rel := by ext n ⟨⟨x, hx⟩, t⟩; exact hx.elim

/-- 元の零行収縮を既存の Kan 境界へ写すと、元の一次段の区間組み立てを回収する。 -/
lemma zeroRowPathContraction_boundary (r : ℕ) (X : StableModel.{u}) :
    zeroRowPathContraction r X ≫ (pointedFullIteratedPathKanBoundary r X).right =
      (β_ ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌))
        (Δ[1] : SSet.{u})).hom ≫
        diagonalAssembly 1 (iteratedSRealizationDiagram r X) ≫ iteratedRealizationToKan r X := by
  rw [zeroRowPathContraction_raw]
  rw [Category.assoc, Category.assoc, ← iteratedBoundaryToKan_comm,
    ← Category.assoc, ← Category.assoc]
  have h : (diagonalZeroColumn (iteratedPathRealizationDiagram r X) ▷
      (Δ[1] : SSet.{u})) ≫ simplicialPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫
        iteratedPathRealizationBoundary r X =
      (β_ ((iteratedPathRealizationDiagram r X).obj (Opposite.op ⦋0⦌))
        (Δ[1] : SSet.{u})).hom ≫ diagonalAssembly 1 (iteratedSRealizationDiagram r X) :=
    simplicialPathDiagonalCylinder_zeroRow_boundary (iteratedSRealizationDiagram r X)
  simpa only [Category.assoc] using congrArg (fun k => k ≫ iteratedRealizationToKan r X) h

end SerrePositivity.KST.SConstruction
