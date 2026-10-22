module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullback

/-!
概要：cospan 模型の二脚の経路と比較二重経路から、模型内の実経路を構成する。
方針：mapping-path と外側の pullback に、経路関手の実 pullback 保存を使う。
規約：両端だけでなく全二重経路を入力する。使われ方：指定境界の経路正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
variable (R : Type u) [CommRing R] {A B C W : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)
  (l : W ⟶ Path.algebra R A) (r : W ⟶ Path.algebra R C)
  (z : W ⟶ Path.algebra R (Path.algebra R B))
  (hs : z ≫ Path.map R (Path.source R B) = l ≫ Path.map R f)
  (ht : z ≫ Path.map R (Path.target R B) = r ≫ Path.map R g)

def pathLiftReplacement : W ⟶ Path.algebra R (MappingPath.algebra R f) :=
  PathPullback.lift R (Path.source R B) f z l hs

lemma pathLiftReplacement_projection : pathLiftReplacement R f l z hs ≫
    Path.map R (MappingPath.projection R f) = l := PathPullback.lift_snd R _ _ _ _ _

lemma pathLiftReplacement_inclusion : pathLiftReplacement R f l z hs ≫
    Path.map R (MappingPath.inclusion R f) = z := PathPullback.lift_fst R _ _ _ _ _

include ht in
lemma pathLiftReplacement_target : pathLiftReplacement R f l z hs ≫
    Path.map R (MappingPath.target R f) = r ≫ Path.map R g := by
  rw [MappingPath.target, Path.map_comp, ← Category.assoc, pathLiftReplacement_inclusion]
  exact ht

def pathLift : W ⟶ Path.algebra R (algebra R f g) :=
  PathPullback.lift R (MappingPath.target R f) g (pathLiftReplacement R f l z hs) r
    (pathLiftReplacement_target R f g l r z hs ht)

lemma pathLift_left : pathLift R f g l r z hs ht ≫ Path.map R (left R f g) = l := by
  rw [left, Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst, pathLiftReplacement_projection]

lemma pathLift_right : pathLift R f g l r z hs ht ≫ Path.map R (right R f g) = r :=
  PathPullback.lift_snd R _ _ _ _ _

lemma pathLift_path : pathLift R f g l r z hs ht ≫ Path.map R (path R f g) = z := by
  rw [path, Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst, pathLiftReplacement_inclusion]

lemma pathLift_source_eq (u : W ⟶ algebra R f g)
    (hl : l ≫ Path.source R A = u ≫ left R f g)
    (hr : r ≫ Path.source R C = u ≫ right R f g)
    (hz : z ≫ Path.source R (Path.algebra R B) = u ≫ path R f g) :
    pathLift R f g l r z hs ht ≫ Path.source R (algebra R f g) = u := by
  apply hom_ext R f g
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_left]; exact hl
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_right]; exact hr
  · rw [Category.assoc, ← Path.map_source, ← Category.assoc, pathLift_path]; exact hz

lemma pathLift_target_eq (u : W ⟶ algebra R f g)
    (hl : l ≫ Path.target R A = u ≫ left R f g)
    (hr : r ≫ Path.target R C = u ≫ right R f g)
    (hz : z ≫ Path.target R (Path.algebra R B) = u ≫ path R f g) :
    pathLift R f g l r z hs ht ≫ Path.target R (algebra R f g) = u := by
  apply hom_ext R f g
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_left]; exact hl
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_right]; exact hr
  · rw [Category.assoc, ← Path.map_target, ← Category.assoc, pathLift_path]; exact hz

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
