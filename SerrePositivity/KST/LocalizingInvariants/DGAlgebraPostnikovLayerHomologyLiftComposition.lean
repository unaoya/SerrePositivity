module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerHomologyLift

/-!
概要：指定ホモロジー射の実層への持ち上げは合成と元の両三角形を保持する。
方針：元の係数同型との整合を使い、集中複体上のホモロジーの忠実性で戻す。
規約：双加群射とはまだ主張しない。使われ方：元の π₂ 逆の実 cochain 三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)}
  [A.X.IsStrictlyLE 0] [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (n : ℤ)

lemma postnikovLayerHomologyLift_comp
    (r : A.X.homology (-(n + 1)) ⟶ B.X.homology (-(n + 1)))
    (s : B.X.homology (-(n + 1)) ⟶ C.X.homology (-(n + 1))) :
    postnikovLayerHomologyLift R n r ≫ postnikovLayerHomologyLift R n s =
      postnikovLayerHomologyLift R n (r ≫ s) := by
  apply postnikovLayer_hom_ext R n
  rw [homologyMap_comp, Category.assoc, postnikovLayerHomologyLift_coefficient,
    ← Category.assoc, postnikovLayerHomologyLift_coefficient,
    postnikovLayerHomologyLift_coefficient, Category.assoc]

lemma postnikovLayerHomologyLift_left_triangle (f : A ⟶ B) (g : A ⟶ C)
    (r : B.X.homology (-(n + 1)) ⟶ C.X.homology (-(n + 1)))
    (h : homologyMap f.hom (-(n + 1)) ≫ r = homologyMap g.hom (-(n + 1))) :
    postnikovLayerMap R f n ≫ postnikovLayerHomologyLift R n r = postnikovLayerMap R g n := by
  calc
    _ = postnikovLayerHomologyLift R n (homologyMap f.hom (-(n + 1))) ≫
        postnikovLayerHomologyLift R n r :=
      congrArg (fun t => t ≫ postnikovLayerHomologyLift R n r)
        (postnikovLayerHomologyLift_of_map R n f).symm
    _ = postnikovLayerHomologyLift R n (homologyMap f.hom (-(n + 1)) ≫ r) :=
      postnikovLayerHomologyLift_comp R n _ _
    _ = postnikovLayerHomologyLift R n (homologyMap g.hom (-(n + 1))) :=
      congrArg (fun t => postnikovLayerHomologyLift R n t) h
    _ = _ := postnikovLayerHomologyLift_of_map R n g

lemma postnikovLayerHomologyLift_right_triangle (f : B ⟶ C) (g : A ⟶ C)
    (r : A.X.homology (-(n + 1)) ⟶ B.X.homology (-(n + 1)))
    (h : r ≫ homologyMap f.hom (-(n + 1)) = homologyMap g.hom (-(n + 1))) :
    postnikovLayerHomologyLift R n r ≫ postnikovLayerMap R f n = postnikovLayerMap R g n := by
  calc
    _ = postnikovLayerHomologyLift R n r ≫
        postnikovLayerHomologyLift R n (homologyMap f.hom (-(n + 1))) :=
      congrArg (fun t => postnikovLayerHomologyLift R n r ≫ t)
        (postnikovLayerHomologyLift_of_map R n f).symm
    _ = postnikovLayerHomologyLift R n (r ≫ homologyMap f.hom (-(n + 1))) :=
      postnikovLayerHomologyLift_comp R n _ _
    _ = postnikovLayerHomologyLift R n (homologyMap g.hom (-(n + 1))) :=
      congrArg (fun t => postnikovLayerHomologyLift R n t) h
    _ = _ := postnikovLayerHomologyLift_of_map R n g

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
