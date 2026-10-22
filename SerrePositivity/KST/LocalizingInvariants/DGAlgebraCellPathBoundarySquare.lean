module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathFixedBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：同じ両端と同じ任意の底経路を持つ二経路を、境界固定の二重経路で結ぶ。
方針：両端と全底経路を保つ境界比較射の上で cell 充填する。
規約：底経路の定数性は不要。使われ方：指定された右経路を保つ自然性の coherence。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : W ⟶ C} (v w : Path.Witness R f g)
  (hb : v.hom ≫ Path.map R p = w.hom ≫ Path.map R p)

include hb in
lemma cellBoundarySquare_condition : v.hom ≫ Path.boundaryMap R p =
    w.hom ≫ Path.boundaryMap R p := by
  apply HomotopyPullbackModel.hom_ext R p p
  · rw [Category.assoc, Path.boundaryMap_source, v.source_eq,
      Category.assoc, Path.boundaryMap_source, w.source_eq]
  · rw [Category.assoc, Path.boundaryMap_target, v.target_eq,
      Category.assoc, Path.boundaryMap_target, w.target_eq]
  · simpa only [Category.assoc, Path.boundaryMap_path] using hb

def cellBoundarySquare : Path.Witness R (cellAugmentation R W ≫ v.hom)
    (cellAugmentation R W ≫ w.hom) :=
  RelativePath.cellPathWitness R (Path.boundaryMap R p) (Path.boundaryMap_surjective R p hs)
    (Path.boundaryMap_quasiIso R p hq) v.hom w.hom (cellBoundarySquare_condition R p v w hb)

lemma cellBoundarySquare_factor {D : Mon (Complex R)}
    (r : HomotopyPullbackModel.algebra R p p ⟶ D) :
    (cellBoundarySquare R p hs hq v w hb).hom ≫ Path.map R (Path.boundaryMap R p ≫ r) =
    (cellAugmentation R W ≫ (v.hom ≫ (Path.boundaryMap R p ≫ r))) ≫ Path.diagonal R D := by
  rw [Path.map_comp, ← Category.assoc, cellBoundarySquare, RelativePath.cellPathWitness_relative]
  simp only [Category.assoc, Path.diagonal_naturality]

lemma cellBoundarySquare_source_trace : (cellBoundarySquare R p hs hq v w hb).hom ≫
    Path.map R (Path.source R C) = (cellAugmentation R W ≫ f) ≫ Path.diagonal R C := by
  rw [← Path.boundaryMap_source R p, cellBoundarySquare_factor,
    Path.boundaryMap_source, v.source_eq]

lemma cellBoundarySquare_target_trace : (cellBoundarySquare R p hs hq v w hb).hom ≫
    Path.map R (Path.target R C) = (cellAugmentation R W ≫ g) ≫ Path.diagonal R C := by
  rw [← Path.boundaryMap_target R p, cellBoundarySquare_factor,
    Path.boundaryMap_target, v.target_eq]

lemma cellBoundarySquare_base_trace : (cellBoundarySquare R p hs hq v w hb).hom ≫
    Path.map R (Path.map R p) =
    (cellAugmentation R W ≫ (v.hom ≫ Path.map R p)) ≫ Path.diagonal R (Path.algebra R B) := by
  rw [← Path.boundaryMap_path R p, cellBoundarySquare_factor, Path.boundaryMap_path]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
