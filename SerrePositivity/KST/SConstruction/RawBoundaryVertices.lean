module
public import SerrePositivity.KST.SConstruction.ObjectRawBoundaryEdges
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # 元の全零境界商の頂点と辺の代表
概要：元の一重 S の全零境界商は頂点が一つであり、その全ての辺は loop を表す。
方針：通常の cofiber の各次数の pushout と、実現の零列全体の零化を使う。
規約：元の core 実現の境界商を使う。使われ方：全ての辺から対象類への生成の帰着。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 通常の cofiber の任意次数の単体は、元の単体または点の像で代表される。 -/
lemma rawCofiber_simplex_cases {A B : SSet.{u}} (i : A ⟶ B) (n : SimplexCategoryᵒᵖ)
    (z : (PointedObject.cofiber i).right.obj n) :
    (∃ b : B.obj n, (PointedObject.cofiberQuotient i).app n b = z) ∨
      ∃ p : (𝟙_ SSet.{u}).obj n, (PointedObject.cofiber i).hom.app n p = z := by
  exact Types.eq_or_eq_of_isPushout ((IsPushout.of_hasPushout i (toUnit A)).map
    ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)) z

/-- 元の全零境界商の任意の頂点は元の商の基点と等しい。 -/
lemma boundaryReducedRealization_vertex_eq (X : StableModel.{u})
    (z : (boundaryReducedRealization 0 X).right _⦋0⦌) :
    z = (boundaryReducedRealization 0 X).basepoint := by
  rcases rawCofiber_simplex_cases (zeroDirectionsFatBoundary 1 X).ι
      (Opposite.op ⦋0⦌) z with ⟨b, rfl⟩ | ⟨p, rfl⟩
  · let a : ((iteratedSRealizationDiagram 0 X).obj (Opposite.op ⦋0⦌)) _⦋0⦌ :=
      (iteratedSRealizationCoordinateIso 0 X).inv.app (Opposite.op ⦋0⦌) b
    have hv := ConcreteCategory.congr_hom (NatTrans.congr_app
      (iteratedSRealizationCoordinateIso 0 X).inv_hom_id (Opposite.op ⦋0⦌)) b
    change (iteratedSRealizationCoordinateIso 0 X).hom.app (Opposite.op ⦋0⦌) a = b at hv
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app
      (iteratedZeroColumn_boundary_zero 0 X) (Opposite.op ⦋0⦌)) a
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, diagonalZeroColumn_zero] at h
    change (boundaryReductionQuotient 0 X).app (Opposite.op ⦋0⦌)
      ((iteratedSRealizationCoordinateIso 0 X).hom.app (Opposite.op ⦋0⦌) a) =
        (boundaryReducedRealization 0 X).basepoint at h
    rw [hv] at h
    exact h
  · exact congrArg ((boundaryReducedRealization 0 X).hom.app (Opposite.op ⦋0⦌))
      (show p = PUnit.unit from by cases p; rfl)

/-- 元の全零境界商には頂点が一つだけある。 -/
instance boundaryReducedRealization_vertex_subsingleton (X : StableModel.{u}) :
    Subsingleton ((boundaryReducedRealization 0 X).right _⦋0⦌) where
  allEq a b := (boundaryReducedRealization_vertex_eq X a).trans
    (boundaryReducedRealization_vertex_eq X b).symm

/-- 元の境界商の任意の辺を、同じ基点を持つ境界定数一次単体として扱う。 -/
def rawBoundaryLoopSimplex (X : StableModel.{u})
    (e : (boundaryReducedRealization 0 X).right _⦋1⦌) :
    ((boundaryReducedRealization 0 X).right).PtSimplex 1
      (boundaryReducedRealization 0 X).basepoint where
  map := SSet.yonedaEquiv.symm e
  comm := by
    apply boundary.hom_ext
    intro i
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_const]
    exact boundaryReducedRealization_vertex_eq X _

end SerrePositivity.KST.SConstruction
