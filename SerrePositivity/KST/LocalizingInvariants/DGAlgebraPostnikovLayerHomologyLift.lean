module

public import SerrePositivity.KST.LocalizingInvariants.ConcentratedComplexHomologyLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerMaps

/-!
概要：元の H⁻⁽ⁿ⁺¹⁾ の指定線形射を、指定係数同型を保つ実 Postnikov 層射へ移す。
方針：両層の厳密集中とホモロジーの充満忠実性を使う。
規約：双加群作用の保存は未主張。使われ方：元の係数逆の実 cochain 射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (n : ℤ)

def postnikovLayerHomologyLift (r : B.X.homology (-(n + 1)) ⟶ C.X.homology (-(n + 1))) :
    postnikovLayer R B n ⟶ postnikovLayer R C n :=
  concentratedHomologyLift R (-(n + 1))
    ((postnikovLayerHomologyIso R B n).hom ≫ r ≫ (postnikovLayerHomologyIso R C n).inv)

lemma postnikovLayerHomologyLift_homology
    (r : B.X.homology (-(n + 1)) ⟶ C.X.homology (-(n + 1))) :
    homologyMap (postnikovLayerHomologyLift R n r) (-(n + 1)) =
      (postnikovLayerHomologyIso R B n).hom ≫ r ≫
        (postnikovLayerHomologyIso R C n).inv :=
  concentratedHomologyLift_homology R _ _

lemma postnikovLayerHomologyLift_coefficient
    (r : B.X.homology (-(n + 1)) ⟶ C.X.homology (-(n + 1))) :
    homologyMap (postnikovLayerHomologyLift R n r) (-(n + 1)) ≫
      (postnikovLayerHomologyIso R C n).hom = (postnikovLayerHomologyIso R B n).hom ≫ r := by
  rw [postnikovLayerHomologyLift_homology]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma postnikovLayer_hom_ext (a b : postnikovLayer R B n ⟶ postnikovLayer R C n)
    (h : homologyMap a (-(n + 1)) ≫ (postnikovLayerHomologyIso R C n).hom =
      homologyMap b (-(n + 1)) ≫ (postnikovLayerHomologyIso R C n).hom) : a = b :=
  concentratedHomology_hom_ext R (-(n + 1)) a b
    ((cancel_mono (postnikovLayerHomologyIso R C n).hom).1 h)

lemma postnikovLayerHomologyLift_of_map (f : B ⟶ C) :
    postnikovLayerHomologyLift R n (homologyMap f.hom (-(n + 1))) =
      postnikovLayerMap R f n := by
  apply postnikovLayer_hom_ext R n
  exact (postnikovLayerHomologyLift_coefficient R n _).trans
    (postnikovLayerHomologyIso_naturality R f n).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
