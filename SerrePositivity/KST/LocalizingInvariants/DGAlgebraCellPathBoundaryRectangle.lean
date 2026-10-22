module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBoundaryRectangle
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathFixedBase

/-!
概要：同じ底経路と指定された両端の比較経路を保つ実二重経路を cell 充填する。
方針：境界比較先の長方形を、端点固定の経路持ち上げへ渡す。
規約：四辺と底の全二重経路を保持する。使われ方：cell 反映と射の合成の自然性。
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
  {f₀ f₁ g₀ g₁ : W ⟶ C} (v : Path.Witness R f₀ g₀) (w : Path.Witness R f₁ g₁)
  (l : Path.Witness R f₀ f₁) (r : Path.Witness R g₀ g₁)
  (hb : v.hom ≫ Path.map R p = w.hom ≫ Path.map R p)
  (hl : l.hom ≫ Path.map R p = (f₀ ≫ p) ≫ Path.diagonal R B)
  (hr : r.hom ≫ Path.map R p = (g₀ ≫ p) ≫ Path.diagonal R B)

def cellBoundaryRectangleSquare : Path.Witness R (cellAugmentation R W ≫ v.hom)
    (cellAugmentation R W ≫ w.hom) :=
  Path.Witness.cellLiftFixedBase R (Path.boundaryMap R p) (Path.boundaryMap_surjective R p hs)
    (Path.boundaryMap_quasiIso R p hq) (boundaryRectangleWitness R p v w l r hb hl hr)

lemma cellBoundaryRectangleSquare_factor {D : Mon (Complex R)}
    (t : HomotopyPullbackModel.algebra R p p ⟶ D) :
    (cellBoundaryRectangleSquare R p hs hq v w l r hb hl hr).hom ≫
      Path.map R (Path.boundaryMap R p ≫ t) =
    cellAugmentation R W ≫ (boundaryRectangleWitness R p v w l r hb hl hr).hom ≫
      Path.map R t := by
  rw [Path.map_comp, ← Category.assoc, cellBoundaryRectangleSquare,
    Path.Witness.cellLiftFixedBase_map, Category.assoc]

lemma cellBoundaryRectangleSquare_source_trace :
    (cellBoundaryRectangleSquare R p hs hq v w l r hb hl hr).hom ≫
      Path.map R (Path.source R C) = cellAugmentation R W ≫ l.hom := by
  rw [← Path.boundaryMap_source R p, cellBoundaryRectangleSquare_factor,
    boundaryRectangleWitness_left]

lemma cellBoundaryRectangleSquare_target_trace :
    (cellBoundaryRectangleSquare R p hs hq v w l r hb hl hr).hom ≫
      Path.map R (Path.target R C) = cellAugmentation R W ≫ r.hom := by
  rw [← Path.boundaryMap_target R p, cellBoundaryRectangleSquare_factor,
    boundaryRectangleWitness_right]

lemma cellBoundaryRectangleSquare_base_trace :
    (cellBoundaryRectangleSquare R p hs hq v w l r hb hl hr).hom ≫
      Path.map R (Path.map R p) =
    cellAugmentation R W ≫ ((v.hom ≫ Path.map R p) ≫ Path.diagonal R (Path.algebra R B)) := by
  rw [← Path.boundaryMap_path R p, cellBoundaryRectangleSquare_factor,
    boundaryRectangleWitness_path, Path.boundaryMap_path]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
