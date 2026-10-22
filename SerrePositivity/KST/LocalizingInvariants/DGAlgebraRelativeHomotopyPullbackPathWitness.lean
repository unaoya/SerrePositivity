module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackPathLift

/-!
概要：相対模型の経路持ち上げが、指定した元の二射を実際に結ぶことを証明する。
方針：模型の両脚と全経路による一意性で、経路の両評価を同定する。
規約：経路成分の評価も入力に含める。使われ方：二重 class 経路からの実輸送比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
variable (R : Type u) [CommRing R] {C B W D T : Mon (Complex R)}
  (p : C ⟶ B) (a : W ⟶ C) (g : D ⟶ C)
  (l : T ⟶ Path.algebra R W) (r : T ⟶ Path.algebra R D)
  (z : T ⟶ Path.algebra R (Path.algebra R C))
  (hs : z ≫ Path.map R (Path.source R C) = l ≫ Path.map R a)
  (ht : z ≫ Path.map R (Path.target R C) = r ≫ Path.map R g)
  (hp : z ≫ Path.map R (Path.map R p) =
    (l ≫ Path.map R (a ≫ p)) ≫ Path.map R (Path.diagonal R B))
  (u v : T ⟶ algebra R p a g)

lemma pathLift_source_eq
    (hl : l ≫ Path.source R W = u ≫ left R p a g)
    (hr : r ≫ Path.source R D = u ≫ right R p a g)
    (hz : z ≫ Path.source R (Path.algebra R C) = u ≫ path R p a g) :
    pathLift R p a g l r z hs ht hp ≫ Path.source R (algebra R p a g) = u := by
  apply hom_ext R p a g
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_left]
    exact hl
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_right]
    exact hr
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_path]
    exact hz

lemma pathLift_target_eq
    (hl : l ≫ Path.target R W = v ≫ left R p a g)
    (hr : r ≫ Path.target R D = v ≫ right R p a g)
    (hz : z ≫ Path.target R (Path.algebra R C) = v ≫ path R p a g) :
    pathLift R p a g l r z hs ht hp ≫ Path.target R (algebra R p a g) = v := by
  apply hom_ext R p a g
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_left]
    exact hl
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_right]
    exact hr
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_path]
    exact hz

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
