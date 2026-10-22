module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullback

/-!
概要：二重経路の整合する二脚を、元の代数 pullback の二重経路に持ち上げる。
方針：一重経路 pullback の普遍射を作り、もう一度経路関手を適用する。
規約：全二重経路の等式を入力し両射影を厳密に保つ。使われ方：affine 二重経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
variable (R : Type u) [CommRing R] {A B D W : Mon (Complex R)} (f : A ⟶ D) (g : B ⟶ D)

def pullbackToPath : MonoidPullback.obj (Path.map R f) (Path.map R g) ⟶
    Path.algebra R (MonoidPullback.obj f g) :=
  lift R f g (MonoidPullback.fst _ _) (MonoidPullback.snd _ _)
    (MonoidPullback.condition _ _)

lemma pullbackToPath_fst : pullbackToPath R f g ≫ Path.map R (MonoidPullback.fst f g) =
    MonoidPullback.fst (Path.map R f) (Path.map R g) := lift_fst R _ _ _ _ _

lemma pullbackToPath_snd : pullbackToPath R f g ≫ Path.map R (MonoidPullback.snd f g) =
    MonoidPullback.snd (Path.map R f) (Path.map R g) := lift_snd R _ _ _ _ _

variable (a : W ⟶ Path.algebra R (Path.algebra R A))
  (b : W ⟶ Path.algebra R (Path.algebra R B))
  (h : a ≫ Path.map R (Path.map R f) = b ≫ Path.map R (Path.map R g))

def doubleLift : W ⟶ Path.algebra R (Path.algebra R (MonoidPullback.obj f g)) :=
  lift R (Path.map R f) (Path.map R g) a b h ≫ Path.map R (pullbackToPath R f g)

lemma doubleLift_fst : doubleLift R f g a b h ≫
    Path.map R (Path.map R (MonoidPullback.fst f g)) = a := by
  rw [doubleLift, Category.assoc, ← Path.map_comp, pullbackToPath_fst]
  exact lift_fst R _ _ _ _ _

lemma doubleLift_snd : doubleLift R f g a b h ≫
    Path.map R (Path.map R (MonoidPullback.snd f g)) = b := by
  rw [doubleLift, Category.assoc, ← Path.map_comp, pullbackToPath_snd]
  exact lift_snd R _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathPullback
