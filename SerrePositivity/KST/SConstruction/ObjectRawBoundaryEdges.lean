module
public import SerrePositivity.KST.SConstruction.ObjectBoundaryTriangle

/-! # Kan 置換前の元の object S₁ の境界商の辺
概要：元の object S の比較と辺を元の境界商へ構成し、Kan 単位で既存の辺を回収する。
方針：元の零列の cofiber 商への降下を使って全頂点の基点条件を証明する。
規約：object S₀ の離散頂点を別に潰さない。使われ方：基本亜群の表示の対象生成元の照合。
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

/-- 元の object S から元の全零境界商への置換前の比較。 -/
def objectRawBoundaryComparison (X : StableModel.{u}) :
    objectSConstruction X.carrier ⟶ (boundaryReducedRealization 0 X).right :=
  objectToCoreSRealization X.carrier ≫ (iteratedSRealizationCoordinateIso 0 X).hom ≫
    boundaryReductionQuotient 0 X

/-- 置換前の比較と Kan 単位の合成は既存の元の比較を回収する。 -/
lemma objectRawBoundaryComparison_kan (X : StableModel.{u}) :
    objectRawBoundaryComparison X ≫
      (PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right =
        objectBoundaryKanComparison X := by
  simp only [objectRawBoundaryComparison, objectBoundaryKanComparison,
    iteratedRealizationToKan, Category.assoc]

/-- 元の実現の零列は Kan 置換前の同じ全零境界商で基点となる。 -/
lemma iteratedZeroColumn_boundary_zero (r : ℕ) (X : StableModel.{u}) :
    diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
      (iteratedSRealizationCoordinateIso r X).hom ≫ boundaryReductionQuotient r X =
        toUnit ((iteratedSRealizationDiagram r X).obj (Opposite.op ⦋0⦌)) ≫
          (boundaryReducedRealization r X).hom := by
  rw [← innerZeroToFullBoundaryComparison_quotient, ← Category.assoc]
  change (diagonalZeroColumn (iteratedSRealizationDiagram r X) ≫
    PointedObject.cofiberQuotient (diagonalZeroColumn (iteratedSRealizationDiagram r X))) ≫
      (innerZeroToFullBoundaryComparison r X).right = _
  rw [PointedObject.cofiberQuotient_condition, Category.assoc, Under.w]

/-- 元の object S の全頂点は、置換前の同じ境界商の基点へ写る。 -/
lemma objectRawBoundaryComparison_vertex (X : StableModel.{u})
    (z : (objectSConstruction X.carrier) _⦋0⦌) :
    (objectRawBoundaryComparison X).app _ z = (boundaryReducedRealization 0 X).basepoint := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (iteratedZeroColumn_boundary_zero 0 X) (Opposite.op ⦋0⦌))
      (⟨z, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
        (X := sConstruction 0 X.carrier) z⟩ : (coreSConstruction 0 X.carrier) _⦋0⦌)
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply, diagonalZeroColumn_zero] at h
  change ((iteratedSRealizationCoordinateIso 0 X).hom ≫ boundaryReductionQuotient 0 X).app
    (Opposite.op ⦋0⦌) ((coreSConstruction 0 X.carrier).map
      (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op ⟨z, _⟩) = _
  have he : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op =
      𝟙 (Opposite.op ⦋0⦌) := Subsingleton.elim _ _
  rw [he, CategoryTheory.Functor.map_id]
  exact h

/-- 元の object S₁ の辺を、置換前の境界商の同じ基点を持つ一次単体とする。 -/
def objectRawBoundaryEdge (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    ((boundaryReducedRealization 0 X).right).PtSimplex 1
      (boundaryReducedRealization 0 X).basepoint where
  map := SSet.yonedaEquiv.symm e ≫ objectRawBoundaryComparison X
  comm := by
    apply boundary.hom_ext
    intro i
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply SSet.yonedaEquiv.injective
    rw [← Category.assoc, SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, SSet.yonedaEquiv_const]
    exact objectRawBoundaryComparison_vertex X _

/-- 元の辺を Kan 単位で写すと既存の Kan 境界商の辺を厳密に回収する。 -/
lemma objectRawBoundaryEdge_kan (X : StableModel.{u})
    (e : (objectSConstruction X.carrier) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (PointedKanReplacement.unit.app (boundaryReducedRealization 0 X)).right rfl
      (objectRawBoundaryEdge X e) = objectBoundaryEdge X e := by
  apply RelativeMorphism.ext
  change (SSet.yonedaEquiv.symm e ≫ objectRawBoundaryComparison X) ≫ _ = _
  rw [Category.assoc, objectRawBoundaryComparison_kan]
  rfl

end SerrePositivity.KST.SConstruction
