module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackExt
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullback

/-!
概要：相対 homotopy pullback の二脚と経路の経路から、実模型内の経路を構成する。
方針：三つの実 pullback に経路関手の pullback 保存を順に適用する。
規約：底を含む全二重経路の式を入力する。使われ方：class 輸送射の二次比較。
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

def pathLiftRelative : T ⟶ Path.algebra R (RelativePath.algebra R p) :=
  PathPullback.lift R (Path.map R p) (Path.diagonal R B) z (l ≫ Path.map R (a ≫ p)) hp

lemma pathLiftRelative_inclusion : pathLiftRelative R p a l z hp ≫
    Path.map R (RelativePath.inclusion R p) = z := PathPullback.lift_fst R _ _ _ _ _

include hs in
lemma pathLiftRelative_source : pathLiftRelative R p a l z hp ≫
    Path.map R (RelativePath.source R p) = l ≫ Path.map R a := by
  rw [RelativePath.source, Path.map_comp, ← Category.assoc, pathLiftRelative_inclusion]
  exact hs

include ht in
lemma pathLiftRelative_target : pathLiftRelative R p a l z hp ≫
    Path.map R (RelativePath.target R p) = r ≫ Path.map R g := by
  rw [RelativePath.target, Path.map_comp, ← Category.assoc, pathLiftRelative_inclusion]
  exact ht

def pathLiftMapping : T ⟶ Path.algebra R (RelativeMappingPath.algebra R p a) :=
  PathPullback.lift R (RelativePath.source R p) a (pathLiftRelative R p a l z hp) l
    (pathLiftRelative_source R p a l z hs hp)

lemma pathLiftMapping_projection : pathLiftMapping R p a l z hs hp ≫
    Path.map R (RelativeMappingPath.projection R p a) = l := PathPullback.lift_snd R _ _ _ _ _

lemma pathLiftMapping_inclusion : pathLiftMapping R p a l z hs hp ≫
    Path.map R (RelativeMappingPath.inclusion R p a) = pathLiftRelative R p a l z hp :=
  PathPullback.lift_fst R _ _ _ _ _

include ht in
lemma pathLiftMapping_target : pathLiftMapping R p a l z hs hp ≫
    Path.map R (RelativeMappingPath.target R p a) = r ≫ Path.map R g := by
  rw [RelativeMappingPath.target, Path.map_comp, ← Category.assoc, pathLiftMapping_inclusion]
  exact pathLiftRelative_target R p a g l r z ht hp

def pathLift : T ⟶ Path.algebra R (algebra R p a g) :=
  PathPullback.lift R (RelativeMappingPath.target R p a) g (pathLiftMapping R p a l z hs hp) r
    (pathLiftMapping_target R p a g l r z hs ht hp)

lemma pathLift_left : pathLift R p a g l r z hs ht hp ≫ Path.map R (left R p a g) = l := by
  rw [left, Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst, pathLiftMapping_projection]

lemma pathLift_right : pathLift R p a g l r z hs ht hp ≫ Path.map R (right R p a g) = r :=
  PathPullback.lift_snd R _ _ _ _ _

lemma pathLift_path : pathLift R p a g l r z hs ht hp ≫ Path.map R (path R p a g) = z := by
  rw [path, Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst, Path.map_comp, ← Category.assoc, pathLiftMapping_inclusion,
    pathLiftRelative_inclusion]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativeHomotopyPullback
