module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackPathLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBoundaryComparison

/-!
概要：同じ底経路の二つの持ち上げと端点比較から、境界比較先の実長方形を構成する。
方針：端点の二経路と底の定数二重経路を、cospan 模型の経路 lift に渡す。
規約：端点比較は底の上で定数。使われ方：cell 比較射の合成を保つ自然性正方形。
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
  {f₀ f₁ g₀ g₁ : W ⟶ C} (v : Path.Witness R f₀ g₀) (w : Path.Witness R f₁ g₁)
  (l : Path.Witness R f₀ f₁) (r : Path.Witness R g₀ g₁)
  (hb : v.hom ≫ Path.map R p = w.hom ≫ Path.map R p)
  (hl : l.hom ≫ Path.map R p = (f₀ ≫ p) ≫ Path.diagonal R B)
  (hr : r.hom ≫ Path.map R p = (g₀ ≫ p) ≫ Path.diagonal R B)

include hl in
lemma boundaryRectangle_source : ((v.hom ≫ Path.map R p) ≫
    Path.diagonal R (Path.algebra R B)) ≫ Path.map R (Path.source R B) =
      l.hom ≫ Path.map R p := by
  have he : (v.hom ≫ Path.map R p) ≫ Path.source R B = f₀ ≫ p := by
    rw [Category.assoc, Path.map_source, ← Category.assoc, v.source_eq]
  rw [Category.assoc, Path.diagonal_naturality, ← Category.assoc, he, hl]

include hr in
lemma boundaryRectangle_target : ((v.hom ≫ Path.map R p) ≫
    Path.diagonal R (Path.algebra R B)) ≫ Path.map R (Path.target R B) =
      r.hom ≫ Path.map R p := by
  have he : (v.hom ≫ Path.map R p) ≫ Path.target R B = g₀ ≫ p := by
    rw [Category.assoc, Path.map_target, ← Category.assoc, v.target_eq]
  rw [Category.assoc, Path.diagonal_naturality, ← Category.assoc, he, hr]

def boundaryRectangleHom : W ⟶ Path.algebra R (HomotopyPullbackModel.algebra R p p) :=
  HomotopyPullbackModel.pathLift R p p l.hom r.hom
    ((v.hom ≫ Path.map R p) ≫ Path.diagonal R (Path.algebra R B))
    (boundaryRectangle_source R p v l hl) (boundaryRectangle_target R p v r hr)

def boundaryRectangleWitness : Path.Witness R (v.hom ≫ Path.boundaryMap R p)
    (w.hom ≫ Path.boundaryMap R p) where
  hom := boundaryRectangleHom R p v l r hl hr
  source_eq := by
    unfold boundaryRectangleHom
    apply HomotopyPullbackModel.pathLift_source_eq
    · rw [l.source_eq, Category.assoc, Path.boundaryMap_source, v.source_eq]
    · rw [r.source_eq, Category.assoc, Path.boundaryMap_target, v.target_eq]
    · rw [Category.assoc, Path.diagonal_source, Category.comp_id,
        Category.assoc, Path.boundaryMap_path]
  target_eq := by
    unfold boundaryRectangleHom
    apply HomotopyPullbackModel.pathLift_target_eq
    · rw [l.target_eq, Category.assoc, Path.boundaryMap_source, w.source_eq]
    · rw [r.target_eq, Category.assoc, Path.boundaryMap_target, w.target_eq]
    · rw [Category.assoc, Path.diagonal_target, Category.comp_id,
        Category.assoc, Path.boundaryMap_path, hb]

lemma boundaryRectangleWitness_left : (boundaryRectangleWitness R p v w l r hb hl hr).hom ≫
    Path.map R (HomotopyPullbackModel.left R p p) = l.hom :=
  HomotopyPullbackModel.pathLift_left R p p l.hom r.hom _
    (boundaryRectangle_source R p v l hl) (boundaryRectangle_target R p v r hr)

lemma boundaryRectangleWitness_right : (boundaryRectangleWitness R p v w l r hb hl hr).hom ≫
    Path.map R (HomotopyPullbackModel.right R p p) = r.hom :=
  HomotopyPullbackModel.pathLift_right R p p l.hom r.hom _
    (boundaryRectangle_source R p v l hl) (boundaryRectangle_target R p v r hr)

lemma boundaryRectangleWitness_path : (boundaryRectangleWitness R p v w l r hb hl hr).hom ≫
    Path.map R (HomotopyPullbackModel.path R p p) =
      (v.hom ≫ Path.map R p) ≫ Path.diagonal R (Path.algebra R B) :=
  HomotopyPullbackModel.pathLift_path R p p l.hom r.hom _
    (boundaryRectangle_source R p v l hl) (boundaryRectangle_target R p v r hr)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
