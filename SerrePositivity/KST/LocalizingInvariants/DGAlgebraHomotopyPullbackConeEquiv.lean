module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMap

/-!
概要：指定された二脚と全乗法的経路を持つ錐を、実経路模型への代数射で表す。
方針：三成分を記録し、既存の lift と hom_ext で互いの逆を証明する。
規約：経路の両端だけへの商は取らない。一般の導来写像空間との比較は別に行う。
使われ方：平方零微分摂動による Postnikov 拡大のパラメータ付き普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C W : Mon (Complex R)}
  (f : A ⟶ B) (g : C ⟶ B)

structure PathCone (W : Mon (Complex R)) where
  left : W ⟶ A
  right : W ⟶ C
  path : W ⟶ Path.algebra R B
  source_eq : path ≫ Path.source R B = left ≫ f
  target_eq : path ≫ Path.target R B = right ≫ g

namespace PathCone

@[ext]
lemma ext {s t : PathCone R f g W} (hl : s.left = t.left)
    (hr : s.right = t.right) (hp : s.path = t.path) : s = t := by
  cases s
  cases t
  cases hl
  cases hr
  cases hp
  rfl

def witness (s : PathCone R f g W) : Path.Witness R (s.left ≫ f) (s.right ≫ g) where
  hom := s.path
  source_eq := s.source_eq
  target_eq := s.target_eq

def precomp {V : Mon (Complex R)} (s : PathCone R f g W) (a : V ⟶ W) :
    PathCone R f g V where
  left := a ≫ s.left
  right := a ≫ s.right
  path := a ≫ s.path
  source_eq := by rw [Category.assoc, s.source_eq, Category.assoc]
  target_eq := by rw [Category.assoc, s.target_eq, Category.assoc]

end PathCone

def homPathCone (a : W ⟶ algebra R f g) : PathCone R f g W where
  left := a ≫ left R f g
  right := a ≫ right R f g
  path := a ≫ path R f g
  source_eq := by rw [Category.assoc, path_source, Category.assoc]
  target_eq := by rw [Category.assoc, path_target, Category.assoc]

def pathConeLift (s : PathCone R f g W) : W ⟶ algebra R f g :=
  lift R f g s.left s.right (s.witness R f g)

@[simp]
lemma pathConeLift_left (s : PathCone R f g W) :
    pathConeLift R f g s ≫ left R f g = s.left := lift_left R _ _ _ _ _

@[simp]
lemma pathConeLift_right (s : PathCone R f g W) :
    pathConeLift R f g s ≫ right R f g = s.right := lift_right R _ _ _ _ _

@[simp]
lemma pathConeLift_path (s : PathCone R f g W) :
    pathConeLift R f g s ≫ path R f g = s.path := lift_path R _ _ _ _ _

def homPathConeEquiv : (W ⟶ algebra R f g) ≃ PathCone R f g W where
  toFun := homPathCone R f g
  invFun := pathConeLift R f g
  left_inv a := by
    apply hom_ext R f g
    · exact pathConeLift_left R f g (homPathCone R f g a)
    · exact pathConeLift_right R f g (homPathCone R f g a)
    · exact pathConeLift_path R f g (homPathCone R f g a)
  right_inv s := by
    apply PathCone.ext R f g
    · exact pathConeLift_left R f g s
    · exact pathConeLift_right R f g s
    · exact pathConeLift_path R f g s

lemma homPathCone_precomp {V : Mon (Complex R)} (a : V ⟶ W)
    (b : W ⟶ algebra R f g) :
    homPathCone R f g (a ≫ b) = (homPathCone R f g b).precomp R f g a := by
  apply PathCone.ext R f g <;> exact Category.assoc _ _ _

lemma pathConeLift_precomp {V : Mon (Complex R)} (a : V ⟶ W)
    (s : PathCone R f g W) :
    pathConeLift R f g (s.precomp R f g a) = a ≫ pathConeLift R f g s := by
  apply hom_ext R f g
  · rw [pathConeLift_left, Category.assoc, pathConeLift_left]; rfl
  · rw [pathConeLift_right, Category.assoc, pathConeLift_right]; rfl
  · rw [pathConeLift_path, Category.assoc, pathConeLift_path]; rfl

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
