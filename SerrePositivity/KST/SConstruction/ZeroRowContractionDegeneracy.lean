module
public import SerrePositivity.KST.SConstruction.ZeroRowPathContraction
public import SerrePositivity.KST.SConstruction.PathZeroColumnSection

/-! # 零行収縮による元の零段の退化像の固定
概要：元の零段の任意の退化像は、零行上の収縮の区間全体で既存の Kan 経路模型の基点に留まる。
方針：退化と零列の合成を定数切断と同定し、商と収縮の基点固定式を合成する。
規約：任意の零段頂点を許す。使われ方：零行の点つき loop 射と fiber 比較の照合。
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

/-- 元の零段の退化像は、Kan 置換前の点つき経路商ですでに厳密に基点へ写る。 -/
lemma zeroRowPathToQuotient_degeneracy (r : ℕ) (X : StableModel.{u}) :
    (iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
        zeroRowPathToQuotient r X =
      toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
        (pointedIteratedPathRealization r X).hom := by
  have h : (iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
      diagonalZeroColumn (iteratedPathRealizationDiagram r X) =
    simplicialPathDiagonalSection (iteratedSRealizationDiagram r X) :=
    simplicialPathZeroColumn_section (iteratedSRealizationDiagram r X)
  change ((iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ≫
    diagonalZeroColumn (iteratedPathRealizationDiagram r X)) ≫ pointedIteratedPathQuotient r X = _
  rw [h]
  exact PointedObject.cofiberQuotient_condition
    (simplicialPathDiagonalSection (iteratedSRealizationDiagram r X))

/-- 元の零段の退化像は零行収縮の全時刻で既存の Kan 経路模型の基点に厳密に留まる。 -/
lemma zeroRowPathContraction_degeneracy (r : ℕ) (X : StableModel.{u}) :
    ((iteratedSRealizationDiagram r X).map (SimplexCategory.σ (0 : Fin 1)).op ▷
        (Δ[1] : SSet.{u})) ≫ zeroRowPathContraction r X =
      toUnit (((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ⊗
        (Δ[1] : SSet.{u})) ≫ ((pointedIteratedPathKanFunctor r).obj X).hom := by
  have hp : ((pointedIteratedPathRealization r X).hom ▷ (Δ[1] : SSet.{u})) ≫
      reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) =
    toUnit ((𝟙_ SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫
      (pointedIteratedPathRealization r X).hom :=
    reducedPathDiagonalCylinder_point (iteratedSRealizationDiagram r X)
  have hu : (pointedIteratedPathRealization r X).hom ≫
      (PointedKanReplacement.unit.app (pointedIteratedPathRealization r X)).right =
    ((pointedIteratedPathKanFunctor r).obj X).hom := Under.w _
  change (_ ▷ (Δ[1] : SSet.{u})) ≫ (zeroRowPathToQuotient r X ▷ (Δ[1] : SSet.{u})) ≫
    reducedPathDiagonalCylinder (iteratedSRealizationDiagram r X) ≫ _ = _
  rw [← comp_whiskerRight_assoc, zeroRowPathToQuotient_degeneracy, comp_whiskerRight_assoc,
    ← Category.assoc ((pointedIteratedPathRealization r X).hom ▷ _), hp]
  simp only [Category.assoc, comp_toUnit_assoc, hu]

end SerrePositivity.KST.SConstruction
