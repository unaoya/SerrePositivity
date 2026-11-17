module

public import SerrePositivity.AlgebraicGeometry.AffineGammaCechCocone
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
概要：同じアフィン nerve の各次数の大域切断と、環の conerve の標準比較。
方針：元の射影を脚とする、同じ二つの余錐の普遍性を使う。
規約：各環からの脚と基底からの head を保持する。
使われ方：元の全ての nerve の射を保つ自然同型への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]

/-- 同じアフィン nerve の各次数の Γ と、元の環の conerve の標準同型。 -/
def affineGammaCechComponentIso (n : SimplexCategory) :
    (Arrow.mk (Scheme.Γ.map f.op)).cechConerve.obj n ≅
      ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).obj n :=
  (colimit.isColimit _).coconePointUniqueUpToIso (affineGammaCechIsColimit f n)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準比較は、各環の脚を元の射影の Γ へ送る。 -/
theorem affineGammaCechComponentIso_ι (n : SimplexCategory) (i : Fin (n.len + 1)) :
    WidePushout.ι (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.map f.op) i ≫
        (affineGammaCechComponentIso f n).hom =
      Scheme.Γ.map (WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) i).op := by
  rw [← affineGammaCechCocone_ι f n i]
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (affineGammaCechIsColimit f n) (some i)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ標準比較は、元の head も同じ基底への射の Γ へ送る。 -/
theorem affineGammaCechComponentIso_head (n : SimplexCategory) :
    WidePushout.head (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.map f.op) ≫
        (affineGammaCechComponentIso f n).hom =
      Scheme.Γ.map (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).op := by
  rw [← affineGammaCechCocone_head f n]
  exact (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (affineGammaCechIsColimit f n) none

end SerrePositivity.AlgebraicGeometry
